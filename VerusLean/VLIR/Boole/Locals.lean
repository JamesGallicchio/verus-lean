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

/-- Base variables of non-init `Assign`s whose LHS is a *projected* place
    (`a[i] = …`, `p.f = …`).  These mutate the base variable even though the
    plain-LHS walk (`collectSetVars`) surfaces no name for them — the
    projected-assign lowering rebuilds the container and stores it back to
    the base.  Needed to shadow by-value `mut` parameters mutated through
    indexing and to re-pin loop length invariants for index-mutated arrays. -/
partial def collectProjectedAssignBases : Stm → List String
  | .Assign lhs _ _ lhsIsInit =>
    if lhsIsInit then []
    else match lvalueVarName? lhs with
      | some _ => []
      | none => (lhs.baseVar?).toList
  | .AssertQuery _ body => collectProjectedAssignBases body
  | .DeadEnd stm => collectProjectedAssignBases stm
  | .If _cond b1 b2 =>
    collectProjectedAssignBases b1 ++ (b2.map collectProjectedAssignBases).getD []
  | .Loop _isForLoop _label cond body _invs _decrease =>
    (match cond with | some (s, _) => collectProjectedAssignBases s | none => [])
      ++ collectProjectedAssignBases body
  | .OpenInvariant stm => collectProjectedAssignBases stm
  | .ClosureInner body => collectProjectedAssignBases body
  | .Block stms => stms.flatMap collectProjectedAssignBases
  | _ => []

/-! ## Filtering -/

def localShouldEmit (_hasForLoop : Bool) (decl : LocalDeclInfo) : Bool :=
  !decl.isSourceDecreases &&
    !shouldDropForLoopScaffoldingLocal decl.name &&
    !isUnitLikeTyp decl.ty

partial def stmHasForLoop : Stm → Bool
  | .Loop true _ _ _ _ _ => true
  | .Block stms => stms.any stmHasForLoop
  | .If _ b1 b2 => stmHasForLoop b1 || (b2.map stmHasForLoop).getD false
  | .DeadEnd stm => stmHasForLoop stm
  | _ => false

mutual
  private partial def recoveredLoopLocalUseBody : RecoveredForLoop → Stm
    | loop =>
      let pre := loop.preStms.map stripForLoopScaffoldingFromBody
      let body := stripForLoopScaffoldingFromBody (.Block loop.userBody)
      let post :=
        loop.postStms.filterMap fun
          | .Assign lhs ty rhs lhsIsInit =>
            if shouldDropAssignAsForLoopScaffolding lhs then
              none
            else
              some (stripForLoopScaffoldingFromBody (.Assign lhs ty rhs lhsIsInit))
          | stm => some (stripForLoopScaffoldingFromBody stm)
      .Block (pre ++ [.Loop true none none body loop.invariants []] ++ post)

  /-- Replace iterator-scaffolding `for` encodings with the recovered
      source-style loop shape before local-use filtering. This keeps temps
      such as `tmp3` that survive into the recovered preamble, while dropping
      scaffolding-only locals (`tmp7`, ghost iterator options, etc.) that are
      no longer mentioned in the emitted Boole body. -/
  partial def stripForLoopScaffoldingFromBody : Stm → Stm
    | .Block stms =>
      match recoverForLoop? stms with
      | some loop => recoveredLoopLocalUseBody loop
      | none => .Block (stms.map stripForLoopScaffoldingFromBody)
    | .If cond b1 b2 =>
      .If cond (stripForLoopScaffoldingFromBody b1)
        (b2.map stripForLoopScaffoldingFromBody)
    | .Loop isFor label cond body invs decrease =>
      .Loop isFor label cond (stripForLoopScaffoldingFromBody body) invs decrease
    | .DeadEnd stm => .DeadEnd (stripForLoopScaffoldingFromBody stm)
    | .OpenInvariant stm => .OpenInvariant (stripForLoopScaffoldingFromBody stm)
    | .ClosureInner body => .ClosureInner (stripForLoopScaffoldingFromBody body)
    | stm => stm
end

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

-- Collect the binder names of every recovered source `for` loop in the
-- body.  The Boole grammar's `for_to_by_statement` binder declares its
-- loop variable inline, so a separate `var i : bv64;` in the procedure's
-- var-block would conflict with "Variable i of type bv64 already in
-- context" at type-check time.  We exclude these names from the emitted
-- locals list.
mutual
  partial def collectForLoopVarNamesStm : Stm → List String
    | .Block stms => collectForLoopVarNamesStms stms
    | .If _ b1 b2 =>
      collectForLoopVarNamesStm b1 ++ (b2.map collectForLoopVarNamesStm).getD []
    | .Loop _ _ cond body _ _ =>
      let condStms := match cond with
        | some (s, _) => collectForLoopVarNamesStm s
        | none => []
      condStms ++ collectForLoopVarNamesStm body
    | .DeadEnd stm => collectForLoopVarNamesStm stm
    | .OpenInvariant stm => collectForLoopVarNamesStm stm
    | .ClosureInner body => collectForLoopVarNamesStm body
    | _ => []

  partial def collectForLoopVarNamesStms : List Stm → List String
    | [] => []
    | stms =>
      match recoverForLoop? stms with
      | some loop =>
        loop.loopVarName :: collectForLoopVarNamesStm (.Block loop.userBody) ++
          collectForLoopVarNamesStms loop.postStms
      | none =>
        match stms with
        | [] => []
        | s :: rest =>
          collectForLoopVarNamesStm s ++ collectForLoopVarNamesStms rest
end

/-- Filter out locals whose names match for-loop binders found in the body. -/
def filterOutForLoopBinders
    (body : Stm) (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  let binders := (collectForLoopVarNamesStm body).eraseDups
  locals.filter (fun decl => !binders.contains decl.name)

end VerusLean.Boole.Locals
