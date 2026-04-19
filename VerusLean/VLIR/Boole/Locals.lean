/-
  Boole.Locals — VLIR-level local-variable analysis.

  Pure inspection over `Stm` / `LocalDeclInfo`: walks a procedure body
  to discover implicit set-vars, dedups source + implicit declarations,
  and filters out (a) decreases artifacts, (b) for-loop scaffolding, and
  (c) locals unreferenced by the post-`normalizeBody` body. No `BuildM`,
  no BooleDDM emission — splitting these out of `Translate.lean` keeps
  the local-set policy together and lets it be reasoned about without
  pulling in the BooleDDM emit machinery.
-/
import Std.Data.HashSet
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.ForLoop
import VerusLean.VLIR.Boole.Normalize

namespace VerusLean.Boole.Locals

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.ForLoop
open VerusLean.Boole.Normalize

/-! ## Constructors -/

def localDecl (name : String) (ty : Typ) (origin : LocalDeclOrigin) : LocalDeclInfo :=
  { name := name, ty := ty, origin := origin }

def localBindings (locals : List LocalDeclInfo) : List (String × Typ) :=
  locals.map LocalDeclInfo.toPair

def dedupLocals (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  let rec go (seen : Std.HashSet String) (acc : List LocalDeclInfo) : List LocalDeclInfo → List LocalDeclInfo
    | [] => acc.reverse
    | decl :: rest =>
      if seen.contains decl.name then go seen acc rest
      else go (seen.insert decl.name) (decl :: acc) rest
  go ∅ [] locals

/-! ## Set-Variable Discovery

    `collectSetVars` walks a body and reports every variable that appears
    as a non-init `Assign` LHS. Used to discover variables Verus mutates
    without an explicit local declaration (e.g. retval slots, `_out`
    aliases for `&mut` parameters), so we can emit `var` bindings for
    them alongside the source-declared locals. -/

partial def collectSetVars : Stm → List LocalDeclInfo
  | .Assign lhs lhsTy _rhs lhsIsInit =>
    if lhsIsInit then []
    else match lvalueVarName? lhs with
      | some name => [localDecl name lhsTy .implicitSet]
      | none => []
  | .AssertQuery _ body => collectSetVars body
  | .DeadEnd stm => collectSetVars stm
  | .If _cond b1 b2 =>
    collectSetVars b1 ++ (b2.map collectSetVars).getD []
  | .Loop _isForLoop _label cond body _invs _decrease =>
    let condVars := match cond with | some (s, _) => collectSetVars s | none => []
    condVars ++ collectSetVars body
  | .OpenInvariant stm => collectSetVars stm
  | .ClosureInner body => collectSetVars body
  | .Block stms => stms.flatMap collectSetVars
  | _ => []

/-! ## Filtering -/

def localShouldEmit (hasForLoop : Bool) (decl : LocalDeclInfo) : Bool :=
  !decl.isSourceDecreases &&
    !shouldDropForLoopScaffoldingLocal decl.name &&
    !(hasForLoop && isForLoopScaffoldingVar decl.name) &&
    !isUnitLikeTyp decl.ty

partial def stmHasForLoop : Stm → Bool
  | .Loop true _ _ _ _ _ => true
  | .Block stms => stms.any stmHasForLoop
  | .If _ b1 b2 => stmHasForLoop b1 || (b2.map stmHasForLoop).getD false
  | .DeadEnd stm => stmHasForLoop stm
  | _ => false

/-- Combine source-declared locals with implicit set-var locals,
    deduplicate, drop anything already covered by inputs/return slots,
    and apply `localShouldEmit` to filter scaffolding/decreases/unit
    types. -/
def collectProcedureLocals
    (sourceLocals : List LocalDeclInfo)
    (inputNames retNames : List String)
    (setVars : List LocalDeclInfo)
    (hasForLoop : Bool := false) : List LocalDeclInfo :=
  let declaredInInputsRetOrLocals := fun (n : String) =>
    inputNames.any (fun x => x == n) ||
    retNames.any (fun x => x == n) ||
    sourceLocals.any (fun decl => decl.name == n)
  let implicitSetLocals := dedupLocals <| setVars.filter (fun decl =>
    !declaredInInputsRetOrLocals decl.name)
  let localsAll := dedupLocals <|
    (sourceLocals.filter (fun decl =>
      !(inputNames.any (fun x => x == decl.name) || retNames.any (fun x => x == decl.name))) ++
      implicitSetLocals)
  localsAll.filter (localShouldEmit hasForLoop)

/-- Drop procedure locals unreferenced by the body. Run after
    `normalizeBody`, so any tmp the translator will eliminate (inlined
    one-shot temps, body-prefix guards hoisted into a Loop's cond) is
    already absent from the body and naturally fails this filter. -/
def filterLocalsByUse
    (body : Stm) (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  locals.filter (fun decl => stmMentionsVar decl.name body)

end VerusLean.Boole.Locals
