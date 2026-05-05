/-
  Boole.Pruning — Drop unreferenced Verus-synthesised impl accessors.

  Verus emits one `->`-accessor spec fn per field per variant
  (`impl&%N::arrow_*`) eagerly for every enum in scope. Most go unused
  in any given test, but we'd translate them all without this pass —
  producing long stretches of never-called `Impl__N_arrow_*` decls that
  bloat the emitted Boole source and slow Strata's verification pass.

  `pruneUnreferencedImpls` keeps an impl accessor only if it's
  transitively reachable from a non-impl decl. Modelled after the boogie
  branch's `pruneUnreferencedSyntheticHelpers` but operating on VLIR
  `Decl`s rather than Core ones.

  Pure: no `BuildM`, no BooleDDM emission. Just a reachability closure
  over `Decl`/`Exp`/`Stm`.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.Pruning

open VerusLean
open VerusLean.Boole.Names

/-- Identify the name prefix Verus uses for auto-generated impl-block
    accessor spec fns. Matches after `identToBoole` sanitisation, which
    preserves `Impl__N_` / `impl__N_` segments. -/
def isSyntheticImplName (s : String) : Bool :=
  s.startsWith "Impl__" || s.startsWith "impl__"

def declIsSyntheticImpl : Decl → Bool
  | .specFn f => isSyntheticImplName (identToBoole f.name)
  | _ => false

def declName? : Decl → Option String
  | .specFn f => some (identToBoole f.name)
  | .proofFn f => some (identToBoole f.name)
  | .execFn f => some (identToBoole f.name)
  | .func f => some (identToBoole f.name)
  | .struct _ | .enum _ | .assertion _ | .mutualBlock _ => none

partial def expCallRefs : Exp → List String
  | .Call fn _ args =>
    let here := identToBoole (CallFun.name fn)
    let rest := args.flatMap expCallRefs
    here :: rest
  | .CallLambda body args =>
    expCallRefs body ++ args.flatMap expCallRefs
  | .StructCtor _ fields => fields.flatMap (fun (_, e) => expCallRefs e)
  | .EnumCtor _ _ fields => fields.flatMap (fun (_, e) => expCallRefs e)
  | .TupleCtor _ data => data.flatMap expCallRefs
  | .Unary _ e => expCallRefs e
  | .Binary _ a b => expCallRefs a ++ expCallRefs b
  | .If c t f => expCallRefs c ++ expCallRefs t ++ expCallRefs f
  | .Bind bind body =>
    let bindRefs := match bind with
      | .Let _ _ rhs => expCallRefs rhs
      | .Quant _ _ trigs => trigs.flatMap (fun g => g.flatMap expCallRefs)
      | .Lambda _ => []
    bindRefs ++ expCallRefs body
  | .ArrayLiteral elems => elems.flatMap expCallRefs
  | .MatchBlock (scrut, _) body => expCallRefs scrut ++ expCallRefs body
  | .Const _ _ | .Var _ => []

partial def stmCallRefs : Stm → List String
  | .Call fn _ args => identToBoole fn :: args.flatMap expCallRefs
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expCallRefs e
  | .AssertBitVector reqs enss =>
    reqs.flatMap expCallRefs ++ enss.flatMap expCallRefs
  | .AssertQuery _ body => stmCallRefs body
  | .Assign _ _ e _ => expCallRefs e
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => stmCallRefs s
  | .Return e? => (e?.map expCallRefs).getD []
  | .BreakOrContinue _ _ | .Reveal .. => []
  | .If cond b1 b2 =>
    expCallRefs cond ++ stmCallRefs b1 ++ (b2.map stmCallRefs).getD []
  | .Loop _ _ cond body invs decrease =>
    let condRefs := match cond with
      | some (s, e) => stmCallRefs s ++ expCallRefs e
      | none => []
    condRefs ++ stmCallRefs body ++ invs.flatMap (fun inv => expCallRefs inv.body) ++
      decrease.flatMap expCallRefs
  | .Block stms => stms.flatMap stmCallRefs

partial def declRefs : Decl → List String
  | .assertion _ => []
  | .specFn f => (f.body.map expCallRefs).getD []
  | .proofFn f =>
    f.requires.flatMap expCallRefs ++ f.ensures.flatMap expCallRefs ++
      (f.body.map stmCallRefs).getD []
  | .execFn f =>
    f.requires.flatMap expCallRefs ++ f.ensures.flatMap expCallRefs ++
      stmCallRefs f.body
  | .func f =>
    f.reqs.flatMap expCallRefs ++ f.postCondition.flatMap expCallRefs
  | .struct _ | .enum _ => []
  | .mutualBlock ds => ds.flatMap declRefs

/-- Fixed-point closure: starting from `seed` impl-names, repeatedly add
    impl-names referenced by kept impl decls until the frontier stabilises. -/
partial def closeImplRefs (implDecls : List Decl)
    (seed : List String) : List String :=
  let rec loop (fuel : Nat) (keep : List String) : List String :=
    match fuel with
    | 0 => keep
    | fuel + 1 =>
      let kept := implDecls.filter (fun d =>
        match declName? d with
        | some n => keep.contains n
        | none => false)
      let next := (keep ++ (kept.flatMap declRefs).filter isSyntheticImplName).eraseDups
      if next.length == keep.length then keep else loop fuel next
  loop (implDecls.length + 1) seed.eraseDups

/-- Drop synthetic impl-block accessor spec fns that no user-level decl
    transitively references. Non-synthetic decls (struct/enum/proofFn/
    execFn/user spec fns/mutualBlocks) are retained unchanged. -/
def pruneUnreferencedImpls (decls : List Decl) : List Decl :=
  let (helpers, others) := decls.partition declIsSyntheticImpl
  let seed := (others.flatMap declRefs).filter isSyntheticImplName
  let kept := closeImplRefs helpers seed
  decls.filter (fun d =>
    if declIsSyntheticImpl d then
      match declName? d with
      | some n => kept.contains n
      | none => true
    else true)

/-- Identify vstd spec fns that came in as uninterpreted (`spec_axioms: null`
    in the JSON) — these are kept after parsing because exec wrappers can
    name them in their `ensures` clauses (e.g. `Slice_spec_slice_len` is
    referenced from `Slice_len`'s ensures, lowered from
    `vstd::slice::spec_slice_len`). Ones that nothing else references should
    still be dropped so they don't leak declarations like
    `Pervasive_exec_invariant` that mention vstd-private types
    (`Pervasive_ExecIter`) we don't translate. -/
def declIsVstdUninterpretedSpec : Decl → Bool
  | .specFn f =>
    f.body.isNone &&
      (let h := Ident.head f.name; h == "Vstd" || h == "vstd")
  | _ => false

/-- `Pervasive_*` helpers (e.g. `Pervasive_arbitrary`,
    `Pervasive_exec_invariant`, `Pervasive_ghost_*`) are auto-synthesized
    by Verus into for-loop measure/invariant clauses.  The translator's
    for-loop recovery strips those clauses from the emitted Boole — but the
    references survive in the IR long enough for `declRefs` to see them.
    Drop their declarations unconditionally so we don't leak dangling
    references to vstd-private types like `Pervasive_ExecIter`. -/
private def isPervasiveScaffoldingBooleName (n : String) : Bool :=
  n.startsWith "Pervasive_"

/-- A vstd spec fn whose calls are all inlined at the call site by
    `expToBoole` (matched by `isPureBooleBuiltinCallName`).  Examples:
    `view`, `Seq.len`, `Vec.len`, `Vec.index`, `cloned`, `Box::new`,
    `Array::array_as_slice`, `Slice::into_vec`, `Clone::clone`,
    `Array::array_index_get`, `Array::array_fill_for_copy_types`.

    Keeping declarations for these would leak return/input type references
    to vstd-private types like `View_V` that we don't translate, since the
    declarations are never actually used in the emitted Boole. -/
def declCallIsInlinedAtCallSite : Decl → Bool
  | .specFn f =>
    isViewName f.name || isSeqLenSpecName f.name || isVecLenSpecName f.name ||
      isVecLenExecName f.name || isVecIndexSpecName f.name ||
      isVecIndexExecName f.name || isClonedName f.name || isBoxNewName f.name ||
      isArrayAsSliceName f.name || isSliceIntoVecName f.name ||
      isCloneExecName f.name || isArrayIndexGetName f.name ||
      isArrayFillForCopyTypesName f.name
  | _ => false

/-- Drop vstd uninterpreted spec fns that no other decl references.  Verus
    pre-inlines autospec wrappers (e.g. `len%returns_clause_autospec`'s body
    `spec_slice_len(slice)` is already substituted into the exec ensures
    before export), so a single-pass reference scan over non-vstd-uninterpreted
    decls is sufficient — no transitive closure through specfn bodies needed.

    Two categories are dropped unconditionally even when they appear
    referenced:
      * `Pervasive_*` scaffolding helpers — their references live inside
        for-loop measure/invariant clauses that the translator strips.
      * Helpers whose calls are inlined at the call site (`view`, `Seq.len`,
        etc.) — their declarations are never actually used in the emitted
        Boole, but their type signatures would leak references to
        vstd-private associated types like `View_V`. -/
def pruneUnreferencedVstdSpecs (decls : List Decl) : List Decl :=
  let referenced :=
    (decls.filter (fun d => !declIsVstdUninterpretedSpec d)).flatMap declRefs
  let referencedSet := referenced.eraseDups
  decls.filter (fun d =>
    if declIsVstdUninterpretedSpec d then
      if declCallIsInlinedAtCallSite d then false
      else
        match declName? d with
        | some n =>
          if isPervasiveScaffoldingBooleName n then false
          else referencedSet.contains n
        | none => false
    else true)

end VerusLean.Boole.Pruning
