/-
  Boole.Reveal — Reveal lowering and type-variable inspection.

  Verus's `reveal(f)` statement asks the verifier to unfold `f`'s body
  inline. Boole has no built-in reveal, so we lower each `reveal(f)` to
  an equivalent universally-quantified equality assumption
  `forall args. f(args) == body(args)`. This lets the SMT backend
  treat the call as transparent at that program point without
  permanently axiomatising the equation.

  Generic spec fns are skipped: their bodies still mention type
  variables, and Boole quantifiers don't bind type vars.
  `specFnIsGenericFull` is the gate; `typTypeVars` / `fnTypeParams` are
  reused by translation orchestration to compute Boole `TypeArgs`.

  Pure: no `BuildM`, no BooleDDM emission. The `Strata.Ann`-valued
  `mkTypeArgsAnn` (BooleDDM-emitting) stays in `Translate.lean` and
  consumes `fnTypeParams` from here.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Inference
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.Reveal

open VerusLean
open VerusLean.Boole.Inference
open VerusLean.Boole.Names

/-- Collect type-variable names referenced in a `Typ`, dedup'd. Used to
    decide which functions need a `TypeArgs` block in Boole and which
    spec fns must be skipped by `mkRevealAssume` (Boole's quantifiers
    don't bind type vars, so a generic spec fn can't be revealed
    point-wise). -/
partial def typTypeVars : Typ → List String
  | .TypParam n => [sanitizeIdent n]
  | .Tuple t1 t2 => (typTypeVars t1 ++ typTypeVars t2).eraseDups
  | .Array t => typTypeVars t
  | .SpecFn ps ret => ((ps.flatMap typTypeVars) ++ typTypeVars ret).eraseDups
  | .Decorated _ t => typTypeVars t
  | .Struct _ ps => (ps.flatMap typTypeVars).eraseDups
  | .Enum _ ps => (ps.flatMap typTypeVars).eraseDups
  | _ => []

def specFnIsGenericFull (f : SpecFn) : Bool :=
  let inputTVars := f.inputs.flatMap (fun (_, ty) => typTypeVars ty)
  let retTVars := typTypeVars f.returnType
  !(inputTVars ++ retTVars).isEmpty

def fnTypeParams (inputs : List (String × Typ)) (ret : Typ) : List String :=
  ((inputs.flatMap (fun (_, ty) => typTypeVars ty)) ++ typTypeVars ret).eraseDups

/-- Lower a `reveal(f)` to a universally-quantified equality
    `forall args. f(args) == body(args)`. Returns `none` for generic
    spec fns (whose type vars Boole's quantifier can't bind) and for
    spec fns without a body. -/
def mkRevealAssume (f : SpecFn) : Option Stm :=
  if specFnIsGenericFull f then none
  else match f.body with
  | none => none
  | some body =>
    let callArgs := f.inputs.map (fun (x, _) => Exp.Var x)
    let call := Exp.Call (.Fun f.name) [] callArgs
    let eq := Exp.Binary (.Eq .Spec) call body
    let equation :=
      if f.inputs.isEmpty then eq
      else Exp.Bind (.Quant .Forall f.inputs []) eq
    some (.Assume equation)

/-- Walk a body replacing every `Reveal fn _fuel` statement with the
    revealed equation (or an empty `Block` if the spec fn is generic /
    bodyless). Recurses into Block / If / DeadEnd / OpenInvariant /
    ClosureInner / AssertQuery / Loop. -/
partial def expandReveals (sfMap : SpecFnMap) : Stm → Stm
  | .Reveal fn _fuel =>
    match sfMap.get? fn with
    | some f => (mkRevealAssume f).getD (.Block [])
    | none => .Block []
  | .Block stms => .Block (stms.map (expandReveals sfMap))
  | .If cond b1 b2 =>
    .If cond (expandReveals sfMap b1) (b2.map (expandReveals sfMap))
  | .DeadEnd stm => .DeadEnd (expandReveals sfMap stm)
  | .OpenInvariant stm => .OpenInvariant (expandReveals sfMap stm)
  | .ClosureInner body => .ClosureInner (expandReveals sfMap body)
  | .AssertQuery mode body => .AssertQuery mode (expandReveals sfMap body)
  | .Loop isFor label cond body invs dec =>
    let cond' := cond.map (fun (s, e) => (expandReveals sfMap s, e))
    .Loop isFor label cond' (expandReveals sfMap body) invs dec
  | s => s

end VerusLean.Boole.Reveal
