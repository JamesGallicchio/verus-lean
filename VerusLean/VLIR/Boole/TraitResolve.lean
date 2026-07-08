/-
  Boole.TraitResolve — point spec-level trait-method calls at the concrete
  impl that implements them.

  An exec call to a trait method arrives already resolved (`resolved_method`
  names the impl).  The spec-level clauses an impl inherits from its trait —
  e.g. `impl&%13::mul`'s `requires mul_req(self, rhs)` — arrive with
  `resolved_method = null`, naming the abstract trait spec fn rather than the
  impl's.  Left that way, a caller sees an uninterpreted predicate, the
  impl's own spec fn (`Impl__12_mul_req`) is dropped as unreferenced, and the
  leftover generic vstd declarations fail SMT encoding.

  This pass rewrites such a call to the impl's spec fn, but only when the
  program contains exactly one impl of that method and the call's type
  arguments are all concrete — the same resolution Verus performs at compile
  time.  A method with two impls (ambiguous) or a call with open type
  parameters is left unchanged.  It runs before pruning, so the reference
  counts pruning consults already point at the impl: the impl's spec fn is
  kept, the abstract trait declaration dropped.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Reveal

namespace VerusLean.Boole.TraitResolve

open VerusLean
open VerusLean.Boole.Names

/-- The type names no type parameter. -/
def typIsConcrete (ty : Typ) : Bool := (Reveal.typTypeVars ty).isEmpty

/-- The `(trait method, impl name)` pair of a `TraitMethodImpl` decl. -/
private def declTraitImpl? : Decl → Option (Ident × Ident)
  | .specFn f => f.traitImplMethod?.map (·, f.name)
  | .execFn f => f.traitImplMethod?.map (·, f.name)
  | _ => none

/-- All `(method, impl)` pairs in the program, including inside
    `mutualBlock`s. -/
private partial def collectTraitImpls : List Decl → List (Ident × Ident)
  | [] => []
  | .mutualBlock ds :: rest => collectTraitImpls ds ++ collectTraitImpls rest
  | d :: rest => (declTraitImpl? d).toList ++ collectTraitImpls rest

/-- Map each trait method (by Boole name) to its unique impl in the program.
    A method with two or more distinct impls is omitted — the target would be
    ambiguous.  A repeated copy of the same impl does not count as a second
    one (Verus can split a program across several JSON files, so an impl may
    appear more than once). -/
def buildTraitImplMap (decls : List Decl) : Std.HashMap String Ident :=
  -- `none` marks a method with ≥ 2 distinct impls.
  let tallied : Std.HashMap String (Option Ident) :=
    (collectTraitImpls decls).foldl (init := {}) fun m (method, impl) =>
      let key := identToBoole method
      match m.get? key with
      | none => m.insert key (some impl)
      | some (some prev) =>
        if identToBoole prev == identToBoole impl then m else m.insert key none
      | some none => m
  Std.HashMap.ofList (tallied.toList.filterMap fun (k, v?) => v?.map (k, ·))

/-- Redirect every trait-method `Exp.Call` the map `m` resolves onto its
    impl, recursing into all subexpressions. -/
partial def rewriteExp (m : Std.HashMap String Ident) : Exp → Exp
  | .Const c ty => .Const c ty
  | .Var v => .Var v
  | .Call fn typs exps =>
    let exps := exps.map (rewriteExp m)
    let fn := match fn with
      | .Fun name =>
        match m.get? (identToBoole name) with
        | some impl => if typs.all typIsConcrete then .Fun impl else .Fun name
        | none => .Fun name
      | other => other
    .Call fn typs exps
  | .CallLambda body args => .CallLambda (rewriteExp m body) (args.map (rewriteExp m))
  | .StructCtor n fields => .StructCtor n (fields.map fun (f, e) => (f, rewriteExp m e))
  | .EnumCtor n v fields => .EnumCtor n v (fields.map fun (f, e) => (f, rewriteExp m e))
  | .TupleCtor n data => .TupleCtor n (data.map (rewriteExp m))
  | .Unary op e => .Unary op (rewriteExp m e)
  | .Binary op a b => .Binary op (rewriteExp m a) (rewriteExp m b)
  | .If c t f => .If (rewriteExp m c) (rewriteExp m t) (rewriteExp m f)
  | .Bind bind body =>
    let bind := match bind with
      | .Let v ty rhs => .Let v ty (rewriteExp m rhs)
      | .Quant q vars trigs => .Quant q vars (trigs.map (·.map (rewriteExp m)))
      | .Lambda vars => .Lambda vars
      | .Choose vars pred => .Choose vars (rewriteExp m pred)
    .Bind bind (rewriteExp m body)
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (rewriteExp m))
  | .MatchBlock (scrut, pat) body => .MatchBlock (rewriteExp m scrut, pat) (rewriteExp m body)

/-- `rewriteExp` lifted over the expressions inside a statement. -/
partial def rewriteStm (m : Std.HashMap String Ident) : Stm → Stm
  | .Call fn typArgs args => .Call fn typArgs (args.map (rewriteExp m))
  | .Assert e => .Assert (rewriteExp m e)
  | .AssertBitVector reqs enss =>
    .AssertBitVector (reqs.map (rewriteExp m)) (enss.map (rewriteExp m))
  | .AssertQuery mode body => .AssertQuery mode (rewriteStm m body)
  | .AssertCompute e => .AssertCompute (rewriteExp m e)
  | .AssertLean e => .AssertLean (rewriteExp m e)
  | .Assume e => .Assume (rewriteExp m e)
  | .Assign lhs lhsTy rhs lhsIsInit => .Assign lhs lhsTy (rewriteExp m rhs) lhsIsInit
  | .DeadEnd s => .DeadEnd (rewriteStm m s)
  | .Return e? => .Return (e?.map (rewriteExp m))
  | .BreakOrContinue label isBreak => .BreakOrContinue label isBreak
  | .If cond b1 b2 => .If (rewriteExp m cond) (rewriteStm m b1) (b2.map (rewriteStm m))
  | .Loop isFor label cond body invs decrease =>
    let cond := cond.map fun (s, e) => (rewriteStm m s, rewriteExp m e)
    let invs := invs.map fun inv => { inv with body := rewriteExp m inv.body }
    .Loop isFor label cond (rewriteStm m body) invs (decrease.map (rewriteExp m))
  | .OpenInvariant s => .OpenInvariant (rewriteStm m s)
  | .ClosureInner s => .ClosureInner (rewriteStm m s)
  | .Block stms => .Block (stms.map (rewriteStm m))
  | .Reveal fn fuel => .Reveal fn fuel

/-- `rewriteExp` / `rewriteStm` lifted over every expression a decl holds
    (body, spec clauses, recommends, decreases). -/
partial def rewriteDecl (m : Std.HashMap String Ident) : Decl → Decl
  | .specFn f => .specFn { f with
      body := f.body.map (rewriteExp m)
      decreases := f.decreases.map (rewriteStm m)
      recommends := f.recommends.map (rewriteExp m) }
  | .proofFn f => .proofFn { f with
      requires := f.requires.map (rewriteExp m)
      ensures := f.ensures.map (rewriteExp m)
      body := f.body.map (rewriteStm m)
      decreases := f.decreases.map (rewriteStm m) }
  | .execFn f => .execFn { f with
      requires := f.requires.map (rewriteExp m)
      ensures := f.ensures.map (rewriteExp m)
      body := rewriteStm m f.body
      decreases := f.decreases.map (rewriteStm m) }
  | .func f => .func { f with
      reqs := f.reqs.map (rewriteExp m)
      postCondition := f.postCondition.map (rewriteExp m) }
  | .mutualBlock ds => .mutualBlock (ds.map (rewriteDecl m))
  | d => d

/-- Point every spec-level call to an abstract trait method — where the
    call's type arguments are concrete — at its unique impl.  No-op when the
    program declares no unambiguous trait-method impls. -/
def resolveTraitSpecCalls (decls : List Decl) : List Decl :=
  let m := buildTraitImplMap decls
  if m.isEmpty then decls else decls.map (rewriteDecl m)

end VerusLean.Boole.TraitResolve
