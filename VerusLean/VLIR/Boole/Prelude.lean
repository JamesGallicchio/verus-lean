/-
  Boole.Prelude — manifests for text-first Boole preludes.

  The prelude files stay textual.  This module records the names that should
  trigger loading those files.  Duplicate filtering still uses the actual names
  returned by parsing the prelude text.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.Prelude

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.Names

/-- Names whose references require `prelude/Seq.boole.st`.

    Generic numeric support such as `nat` and `int_to_nat` is intentionally
    omitted even though the Seq prelude defines it for its own bodies; those
    names are translator support, not Seq-specific triggers. -/
def seqTriggerNames : List String :=
  ["Set", "Set_finite",
   "Seq_len", "Seq_lib_insert", "Seq_new", "Seq_lib_map",
   "Seq_lib_map_values", "Seq_lib_filter", "Seq_lib_sort_by",
   "Seq_lib_zip_with", "Seq_lib_to_set"]

/-- Names whose references require `prelude/Vec.boole.st`. -/
def vecTriggerNames : List String :=
  ["Vec", "Vec_ctor", "Vec_data", "Vec_len", "Vec_index", "Vec_view"]

def seqDirectBuiltinNames : List String :=
  ["Seq_index", "Seq_update", "Seq_push", "Seq_take", "Seq_skip", "Seq_add",
   "Seq_first", "Seq_last", "Seq_subrange", "Seq_lib_contains",
   "Seq_lib_drop_last", "Seq_lib_remove", "Seq_empty"]

def seqTyp (elem : Typ) : Typ :=
  Typ.Struct (.str (.str .anonymous "vstd") "Seq") [elem]

def setTyp (elem : Typ) : Typ :=
  Typ.Struct (.str (.str .anonymous "vstd") "Set") [elem]

def vecTyp (elem : Typ) : Typ :=
  Typ.Struct (.str (.str .anonymous "vstd") "Vec") [elem]

def seqKnownSignatures : List (String × (List Typ × Typ)) :=
  let t := Typ.TypParam "T"
  let a := Typ.TypParam "A"
  let b := Typ.TypParam "B"
  let seqT := seqTyp t
  let setT := setTyp t
  [ ("Seq_index",         ([seqT, .Int], t))
  , ("Seq_update",        ([seqT, .Int, t], seqT))
  , ("Seq_push",          ([seqT, t], seqT))
  , ("Seq_take",          ([seqT, .Int], seqT))
  , ("Seq_skip",          ([seqT, .Int], seqT))
  , ("Seq_add",           ([seqT, seqT], seqT))
  , ("Seq_first",         ([seqT], t))
  , ("Seq_last",          ([seqT], t))
  , ("Seq_subrange",      ([seqT, .Int, .Int], seqT))
  , ("Seq_lib_contains",  ([seqT, t], .Bool))
  , ("Seq_lib_drop_last", ([seqT], seqT))
  , ("Seq_lib_remove",    ([seqT, .Int], seqT))
  , ("Seq_len",           ([seqT], .Nat))
  , ("Seq_lib_insert",    ([seqT, .Int, t], seqT))
  , ("Seq_new",           ([.Nat, .SpecFn [.Int] t], seqT))
  , ("Seq_lib_map",       ([seqTyp a, .SpecFn [.Int, a] b], seqTyp b))
  , ("Seq_lib_map_values",([seqTyp a, .SpecFn [a] b], seqTyp b))
  , ("Seq_lib_filter",    ([seqT, .SpecFn [t] .Bool], seqT))
  , ("Seq_lib_sort_by",   ([seqT, .SpecFn [t, t] .Bool], seqT))
  , ("Seq_lib_zip_with",  ([seqTyp a, seqTyp b], seqTyp (.Tuple a b)))
  , ("Seq_lib_to_set",    ([seqT], setT))
  , ("Set_finite",        ([setT], .Bool))
  ]

def vecKnownSignatures : List (String × (List Typ × Typ)) :=
  let t := Typ.TypParam "T"
  let seqT := seqTyp t
  let vecT := vecTyp t
  [ ("Vec_len",   ([vecT], .USize))
  , ("Vec_index", ([vecT, .USize], t))
  , ("Vec_view",  ([vecT], seqT))
  ]

def knownPreludeSignatures : List (String × (List Typ × Typ)) :=
  seqKnownSignatures ++ vecKnownSignatures

def needsSeqPrelude (referencedNames : List String) : Bool :=
  seqTriggerNames.any (fun n => referencedNames.contains n) ||
    referencedNames.any (fun n => n == "Sequence" || n.startsWith "Sequence.")

def needsVecPrelude (referencedNames : List String) : Bool :=
  vecTriggerNames.any (fun n => referencedNames.contains n)

private def refsOfTyp : Typ → List String
  | .Empty | .Unit | .Bool | .Int | .Nat | .UInt _ | .SInt _ | .USize | .ISize
  | .Char | .StrSlice => []
  | .Array t _ => refsOfTyp t
  | .Tuple t1 t2 => (refsOfTyp t1 ++ refsOfTyp t2).eraseDups
  | .TypParam _ => []
  | .SpecFn params ret => ((params.flatMap refsOfTyp) ++ refsOfTyp ret).eraseDups
  | .Decorated _ ty => refsOfTyp ty
  | .Struct name params =>
    let paramRefs := params.flatMap refsOfTyp
    let selfRefs :=
      -- `vec2seq` branch: Vec is translated as Sequence, so any
      -- Vec-typed reference needs the Sequence prelude (not the Vec
      -- prelude, which would drag in view-axioms we're trying to skip).
      if isVecTypeName name then ["Sequence"]
      else if datatypeNameOf name == "Set" then ["Set"]
      else []
    (selfRefs ++ paramRefs).eraseDups
  | .Enum name params =>
    let paramRefs := params.flatMap refsOfTyp
    let selfRefs := if datatypeNameOf name == "Set" then ["Set"] else []
    (selfRefs ++ paramRefs).eraseDups
  | .AirNamed _ => []

private partial def refsOfExp : Exp → List String
  | .Const _ _ | .Var _ => []
  | .Call fn _ args =>
    let fname := CallFun.name fn
    let fnameStr := identToBoole fname
    let ownRefs :=
      -- `vec2seq` branch: Vec operations collapse to Sequence.* ops,
      -- so their refs trigger the Sequence prelude (not the Vec prelude).
      if isSeqLenSpecName fname || isVecLenSpecName fname || isVecLenExecName fname then ["Sequence"]
      else if isVecIndexSpecName fname || isVecIndexExecName fname then ["Sequence"]
      else if isViewName fname then ["Sequence"]
      else if seqDirectBuiltinNames.contains fnameStr then ["Sequence"]
      else if seqTriggerNames.contains fnameStr then [fnameStr]
      else []
    (ownRefs ++ args.flatMap refsOfExp).eraseDups
  | .CallLambda body args => (refsOfExp body ++ args.flatMap refsOfExp).eraseDups
  | .StructCtor dt fields =>
    -- `vec2seq` branch: Vec ctor (rare in practice — Verus usually goes
    -- through `Vec::new()` calls, not struct-literal ctors) still needs
    -- Sequence prelude since Vec is translated as Sequence.
    let ownRefs := if isVecTypeName dt then ["Sequence"] else []
    (ownRefs ++ fields.flatMap (fun (_, e) => refsOfExp e)).eraseDups
  | .EnumCtor dt _ fields =>
    let ownRefs := if datatypeNameOf dt == "Set" then ["Set"] else []
    (ownRefs ++ fields.flatMap (fun (_, e) => refsOfExp e)).eraseDups
  | .TupleCtor _ elems => (elems.flatMap refsOfExp).eraseDups
  | .Unary _ e => refsOfExp e
  | .Binary _ e1 e2 => (refsOfExp e1 ++ refsOfExp e2).eraseDups
  | .If c t f => (refsOfExp c ++ refsOfExp t ++ refsOfExp f).eraseDups
  | .Bind bind body =>
    let bindRefs := match bind with
      | .Let _ ty rhs => refsOfTyp ty ++ refsOfExp rhs
      | .Quant _ vars trigs =>
        vars.flatMap (fun v => refsOfTyp v.2) ++ trigs.flatMap (fun g => g.flatMap refsOfExp)
      | .Lambda vars => vars.flatMap (fun v => refsOfTyp v.2)
      | .Choose vars pred => vars.flatMap (fun v => refsOfTyp v.2) ++ refsOfExp pred
    (bindRefs ++ refsOfExp body).eraseDups
  | .ArrayLiteral elems => ("Sequence" :: elems.flatMap refsOfExp).eraseDups
  | .MatchBlock (scrut, ty) body => (refsOfExp scrut ++ refsOfTyp ty ++ refsOfExp body).eraseDups

private partial def refsOfLValue : LValue → List String
  | .Var _ => []
  | .Proj base dt _ _ _ _ =>
    let ownRefs := if isVecTypeName dt then ["Vec"] else []
    (ownRefs ++ refsOfLValue base).eraseDups
  | .Proj' base _ _ => refsOfLValue base

private partial def refsOfStm : Stm → List String
  | .Call fn _ args =>
    let fname := fn
    let fnameStr := identToBoole fname
    let ownRefs :=
      -- `vec2seq` branch: Vec operations collapse to Sequence.* ops,
      -- so their refs trigger the Sequence prelude (not the Vec prelude).
      if isSeqLenSpecName fname || isVecLenSpecName fname || isVecLenExecName fname then ["Sequence"]
      else if isVecIndexSpecName fname || isVecIndexExecName fname then ["Sequence"]
      else if isViewName fname then ["Sequence"]
      else if seqDirectBuiltinNames.contains fnameStr then ["Sequence"]
      else if seqTriggerNames.contains fnameStr then [fnameStr]
      else []
    (ownRefs ++ args.flatMap refsOfExp).eraseDups
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => refsOfExp e
  | .AssertBitVector reqs enss => (reqs.flatMap refsOfExp ++ enss.flatMap refsOfExp).eraseDups
  | .AssertQuery _ body => refsOfStm body
  | .Assign lhs lhsTy rhs _ => (refsOfLValue lhs ++ refsOfTyp lhsTy ++ refsOfExp rhs).eraseDups
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => refsOfStm s
  | .Return e? => e?.map refsOfExp |>.getD []
  | .BreakOrContinue _ _ | .Reveal .. => []
  | .If cond b1 b2 => (refsOfExp cond ++ refsOfStm b1 ++ (b2.map refsOfStm).getD []).eraseDups
  | .Loop _ _ cond body invs decrease =>
    let condRefs := match cond with
      | some (s, e) => refsOfStm s ++ refsOfExp e
      | none => []
    (condRefs ++ refsOfStm body ++ invs.flatMap (fun inv => refsOfExp inv.body) ++
      decrease.flatMap refsOfExp).eraseDups
  | .Block stms => (stms.flatMap refsOfStm).eraseDups

private def refsOfSpecFn (f : SpecFn) : List String :=
  (f.inputs.flatMap (fun input => refsOfTyp input.2) ++ refsOfTyp f.returnType ++
    (f.body.map refsOfExp).getD []).eraseDups

private def refsOfProofFn (f : ProofFn) : List String :=
  (f.inputs.flatMap (fun input => refsOfTyp input.2) ++ refsOfTyp f.returnType ++
    f.requires.flatMap refsOfExp ++ f.ensures.flatMap refsOfExp ++
    (f.body.map refsOfStm).getD [] ++ f.locals.flatMap (fun ldecl => refsOfTyp ldecl.ty)).eraseDups

private def refsOfExecFn (f : ExecFn) : List String :=
  (f.inputs.flatMap (fun input => refsOfTyp input.2) ++ refsOfTyp f.returnType ++
    f.requires.flatMap refsOfExp ++ f.ensures.flatMap refsOfExp ++ refsOfStm f.body ++
    f.locals.flatMap (fun ldecl => refsOfTyp ldecl.ty)).eraseDups

private def refsOfFunc (f : FuncCheckSst) : List String :=
  (f.decls.flatMap (fun decl => refsOfTyp decl.2) ++ f.reqs.flatMap refsOfExp ++
    f.postCondition.flatMap refsOfExp).eraseDups

partial def referencedPreludeTriggersOfDecl : Decl → List String
  | .assertion _ => []
  | .specFn f => refsOfSpecFn f
  | .proofFn f => refsOfProofFn f
  | .execFn f => refsOfExecFn f
  | .func f => refsOfFunc f
  | .struct s => (s.fields.flatMap (fun field => refsOfTyp field.2)).eraseDups
  | .enum e =>
    e.fields.flatMap (fun field =>
      match field with
      | .labeled _ fields => fields.flatMap (fun field => refsOfTyp field.2)
      | .tuple _ tys => tys.flatMap refsOfTyp) |>.eraseDups
  | .mutualBlock ds => (ds.flatMap referencedPreludeTriggersOfDecl).eraseDups

def referencedPreludeTriggers (decls : List Decl) : List String :=
  (decls.flatMap referencedPreludeTriggersOfDecl).eraseDups

structure PreludePlan where
  referencedNames : List String
  needsSeq : Bool
  needsVec : Bool

def planDecls (decls : List Decl) : PreludePlan :=
  let refs := referencedPreludeTriggers decls
  { referencedNames := refs
    needsSeq := needsSeqPrelude refs
    needsVec := needsVecPrelude refs }

end VerusLean.Boole.Prelude
