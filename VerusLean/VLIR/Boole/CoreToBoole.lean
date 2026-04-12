/-
  Boole.CoreToBoole — Bridge from Core AST to BooleDDM AST.

  Converts a `Core.Program` (produced by ToCore) into `BooleDDM.Command`
  arrays, which can then be assembled into a `Strata.Program` via Emit.

  This module exists as a transitional bridge: eventually, the translator
  will produce BooleDDM directly and this file will be deleted.
-/
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.ToCore

namespace VerusLean.Boole.CoreToBoole

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Builder
open VerusLean.Boole.Emit
open VerusLean.ToCore
open Core
open Lambda

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩
private def noLabel : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none
private def someLabel (s : String) : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  ann (some (.label default (ann s)))

/-! ## Core Expression → BooleDDM Expression -/

private def collectApps : CoreExpr → CoreExpr × List CoreExpr
  | .app _ fn arg =>
    let (h, args) := collectApps fn
    (h, args ++ [arg])
  | e => (e, [])

private def ppId (id : CoreIdent) : String := CoreIdent.toPretty id

private partial def coreMonoTyToBoole : LMonoTy → BuildM BType
  | .ftvar name => do
    let idx ← resolveFreeVar name
    pure (fvarTy idx)
  | .bitvec 1 => pure (bvTy 1)
  | .bitvec 8 => pure (bvTy 8)
  | .bitvec 16 => pure (bvTy 16)
  | .bitvec 32 => pure (bvTy 32)
  | .bitvec 64 => pure (bvTy 64)
  | .bitvec w => throw s!"unsupported bitvector width: {w}"
  | .tcons name args => do
    match name, args with
    | "bool", [] => pure boolTy
    | "int", [] => pure intTy
    | "string", [] => pure strTy
    | "real", [] => pure intTy
    | "Map", [range, domain] =>
      pure (mapTy (← coreMonoTyToBoole domain) (← coreMonoTyToBoole range))
    | "Sequence", [elem] =>
      pure (seqTy (← coreMonoTyToBoole elem))
    | _, _ =>
      let idx ← resolveFreeVar name
      let args' ← args.toArray.mapM coreMonoTyToBoole
      pure (fvarTy idx args')

private def coreTyToBoole : LTy → BuildM BType
  | .forAll _ monoTy => coreMonoTyToBoole monoTy

private def resolveVar (name : String) : BuildM BExpr := do
  match ← lookupBoundVar name with
  | some idx => pure (Builder.bvar idx)
  | none =>
    let idx ← resolveFreeVar name
    pure (Builder.fvar idx)

/-- Parse a bitvector operator name like "Bv64.Add" into (width, opName). -/
private def parseBvBinaryOp (name : String) : Option (Nat × String) := do
  let parts := name.splitOn "."
  match parts with
  | [sizeStr, opName] =>
    if sizeStr.startsWith "Bv" then
      let w ← (sizeStr.drop 2).toNat?
      some (w, opName)
    else
      none
  | _ => none

private def dispatchBvBinOp (w : Nat) (op : String) (a b : BExpr) : BuildM BExpr :=
  match op with
  | "Add" => pure (bvAdd w a b)
  | "Sub" => pure (bvSub w a b)
  | "Mul" => pure (bvMul w a b)
  | "UDiv" => pure (bvUDiv w a b)
  | "UMod" => pure (bvUMod w a b)
  | "SDiv" => pure (bvSDiv w a b)
  | "SMod" => pure (bvSMod w a b)
  | "And" => pure (bvAnd w a b)
  | "Or" => pure (bvOr w a b)
  | "Xor" => pure (bvXor w a b)
  | "Shl" => pure (bvShl w a b)
  | "UShr" => pure (bvUShr w a b)
  | "ULe" => pure (bvUle w a b)
  | "ULt" => pure (bvUlt w a b)
  | "UGe" => pure (bvUge w a b)
  | "UGt" => pure (bvUgt w a b)
  | "SLe" => pure (bvSle w a b)
  | "SLt" => pure (bvSlt w a b)
  | "SGe" => pure (bvSge w a b)
  | "SGt" => pure (bvSgt w a b)
  | _ => throw s!"unsupported bitvector operation: Bv{w}.{op}"

private def dispatchBvUnaryOp (name : String) (a : BExpr) : Option BExpr :=
  match parseBvBinaryOp name with
  | some (w, "Not") => some (Builder.bvNot w a)
  | some (w, "Neg") => some (Builder.bvNeg w a)
  | _ => none

private partial def dispatchOp (name : String) (args : List BExpr) : BuildM BExpr := do
  match name, args with
  -- Unary
  | "old", [a] => pure (Builder.old a)
  | "Int.Neg", [a] => pure (intNeg a)
  | "Bool.Not", [a] => pure (boolNot a)
  | "Sequence.length", [a] => pure (seqLength a)
  -- Binary: int/real arithmetic
  | "Int.Add", [a, b] => pure (intAdd a b)
  | "Int.Sub", [a, b] => pure (intSub a b)
  | "Int.Mul", [a, b] => pure (intMul a b)
  | "Int.Div", [a, b] => pure (intDiv a b)
  | "Int.Mod", [a, b] => pure (intMod a b)
  -- Binary: int/real comparisons
  | "Int.Le", [a, b] => pure (intLe a b)
  | "Int.Lt", [a, b] => pure (intLt a b)
  | "Int.Ge", [a, b] => pure (intGe a b)
  | "Int.Gt", [a, b] => pure (intGt a b)
  -- Binary: boolean
  | "Bool.And", [a, b] => pure (boolAnd a b)
  | "Bool.Or", [a, b] => pure (boolOr a b)
  | "Bool.Implies", [a, b] => pure (boolImplies a b)
  | "Bool.Equiv", [a, b] => pure (boolEquiv a b)
  -- Unary: bitvector (try by prefix)
  | _, [a] =>
    match dispatchBvUnaryOp name a with
    | some e => pure e
    | none =>
      let fnIdx ← resolveFreeVar name
      pure (Builder.app (Builder.fvar fnIdx) a)
  -- Binary: bitvector (try by prefix)
  | _, [a, b] =>
    match parseBvBinaryOp name with
    | some (w, op) => dispatchBvBinOp w op a b
    | none =>
      let fnIdx ← resolveFreeVar name
      pure ([a, b].foldl (fun acc arg => Builder.app acc arg) (Builder.fvar fnIdx))
  -- Fallback: function application
  | _, _ => do
    let fnIdx ← resolveFreeVar name
    pure (args.foldl (fun acc arg => Builder.app acc arg) (Builder.fvar fnIdx))

private partial def exprToBoole : CoreExpr → BuildM BExpr
  | .fvar _ id _ => resolveVar (ppId id)
  | .bvar _ idx => pure (Builder.bvar idx)
  | .const _ (.boolConst b) => pure (boolConst b)
  | .const _ (.intConst n) => pure (intConst n)
  | .const _ (.bitvecConst w bv) => pure (bitvecConst w bv)
  | .const _ (.strConst s) => pure (.strLit default (ann s))
  | .const _ (.realConst r) =>
    -- Approximate: emit as int for now
    pure (intConst r.num)
  | .eq _ lhs rhs => do
    pure (Builder.eq (← exprToBoole lhs) (← exprToBoole rhs))
  | .ite _ c t e => do
    pure (Builder.ite (← exprToBoole c) (← exprToBoole t) (← exprToBoole e))
  | .quant _ q name ty? _trigger body => do
    let ty' ← match ty? with
      | some monoTy => coreMonoTyToBoole monoTy
      | none => pure unknownTy
    let qName := if name.isEmpty then "__q" else name
    let body' ← withScope do
      addBoundVars #[qName]
      exprToBoole body
    let binds := #[(qName, ty')]
    match q with
    | .all => pure (forallExpr binds body')
    | .exist => pure (existsExpr binds body')
  | .abs _ name ty? body => do
    let ty' ← match ty? with
      | some monoTy => coreMonoTyToBoole monoTy
      | none => pure unknownTy
    let body' ← withScope do
      addBoundVars #[name]
      exprToBoole body
    pure (forallExpr #[(name, ty')] body')
  | .op _ id _ => do
    -- A bare operator with no arguments: treat as a free variable reference
    let idx ← resolveFreeVar (ppId id)
    pure (Builder.fvar idx)
  | e@(.app ..) => do
    let (head, args) := collectApps e
    match head with
    | .op _ id _ =>
      let name := ppId id
      let args' ← args.mapM exprToBoole
      dispatchOp name args'
    | .fvar _ id _ =>
      let fnExpr ← resolveVar (ppId id)
      let args' ← args.mapM exprToBoole
      pure (args'.foldl (fun acc arg => Builder.app acc arg) fnExpr)
    | _ => do
      let fn ← exprToBoole head
      let args' ← args.mapM exprToBoole
      pure (args'.foldl (fun acc arg => Builder.app acc arg) fn)

/-! ## Core Statement → BooleDDM Statement -/

private partial def stmtToBoole : Statement → BuildM BStmt
  | .cmd (.cmd (.init name ty (.det e) _)) => do
    let ty' ← coreTyToBoole ty
    let e' ← exprToBoole e
    let nameStr := ppId name
    let out := initStmt nameStr ty' e'
    pushBoundVar nameStr
    pure out
  | .cmd (.cmd (.init name ty .nondet _)) => do
    let ty' ← coreTyToBoole ty
    let nameStr := ppId name
    let out := varStmt nameStr ty'
    pushBoundVar nameStr
    pure out
  | .cmd (.cmd (.set name (.det e) _)) => do
    pure (setStmt (ppId name) (← exprToBoole e))
  | .cmd (.cmd (.set name .nondet _)) =>
    pure (havocStmt (ppId name))
  | .cmd (.cmd (.assert label e _)) => do
    pure (assertStmt label (← exprToBoole e))
  | .cmd (.cmd (.assume label e _)) => do
    pure (assumeStmt label (← exprToBoole e))
  | .cmd (.cmd (.cover label e _)) => do
    pure (coverStmt label (← exprToBoole e))
  | .cmd (.call lhs pname args _) => do
    let args' ← args.toArray.mapM exprToBoole
    pure (callStmt (lhs.toArray.map ppId) pname args')
  | .block label ss _ => do
    let body ← withScope do ss.mapM stmtToBoole
    pure (blockStmt label body.toArray)
  | .ite (.det cond) t e _ => do
    let cond' ← exprToBoole cond
    let t' ← withScope do t.mapM stmtToBoole
    let e' ← withScope do e.mapM stmtToBoole
    pure (iteStmt cond' t'.toArray e'.toArray)
  | .ite .nondet t e _ => do
    let t' ← withScope do t.mapM stmtToBoole
    let e' ← withScope do e.mapM stmtToBoole
    pure (iteStmt (boolConst true) t'.toArray e'.toArray)
  | .loop (.det guard) measure invs body _ => do
    let guard' ← exprToBoole guard
    let measure' ← match measure with
      | some m => pure (some (← exprToBoole m))
      | none => pure none
    let invs' ← invs.toArray.mapM exprToBoole
    let body' ← withScope do body.mapM stmtToBoole
    pure (whileStmt guard' measure' invs' body'.toArray)
  | .loop .nondet measure invs body _ => do
    let measure' ← match measure with
      | some m => pure (some (← exprToBoole m))
      | none => pure none
    let invs' ← invs.toArray.mapM exprToBoole
    let body' ← withScope do body.mapM stmtToBoole
    pure (whileStmt (boolConst true) measure' invs' body'.toArray)
  | .exit label _ => pure (exitStmt label)
  | .funcDecl _ _ => throw "statement-level function declarations not supported in Boole bridge"
  | .typeDecl _ _ => throw "statement-level type declarations not supported in Boole bridge"

/-! ## Core Declarations → BooleDDM Commands -/

private def mkMonoInputs (inputs : List (CoreIdent × LMonoTy)) :
    BuildM (BooleDDM.Bindings SourceRange × Array String) := do
  let mut bindings : Array (BooleDDM.Binding SourceRange) := #[]
  let mut names : Array String := #[]
  for (id, ty) in inputs do
    let name := ppId id
    let ty' ← coreMonoTyToBoole ty
    bindings := bindings.push
      (BooleDDM.Binding.mkBinding default (ann name) (BooleDDM.TypeP.expr ty'))
    names := names.push name
  pure (BooleDDM.Bindings.mkBindings default (ann bindings), names)

private def mkMonoOutputs (outputs : List (CoreIdent × LMonoTy)) :
    BuildM (Option (BooleDDM.MonoDeclList SourceRange) × Array String) := do
  if outputs.isEmpty then
    pure (none, #[])
  else
    let first := outputs.head!
    let firstName := ppId first.1
    let firstTy ← coreMonoTyToBoole first.2
    let init := MonoDeclList.monoDeclAtom default
      (MonoBind.mono_bind_mk default (ann firstName) firstTy)
    let (result, names) ← outputs.tail.foldlM (fun (acc, names) (id, ty) => do
      let name := ppId id
      let ty' ← coreMonoTyToBoole ty
      pure (MonoDeclList.monoDeclPush default acc
        (MonoBind.mono_bind_mk default (ann name) ty'),
        names.push name))
      (init, #[firstName])
    pure (some result, names)

private def mkSpecElts (spec : Procedure.Spec) : BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  -- Requires
  for (_, check) in spec.preconditions.toList do
    let e ← exprToBoole check.expr
    elts := elts.push (.requires_spec default noLabel (ann none) e)
  -- Ensures
  for (_, check) in spec.postconditions.toList do
    let e ← exprToBoole check.expr
    elts := elts.push (.ensures_spec default noLabel (ann none) e)
  -- Modifies
  if !spec.modifies.isEmpty then
    let modNames := spec.modifies.toArray.map (fun id => ann (ppId id))
    elts := elts.push (.modifies_spec default (ann modNames))
  pure elts

private partial def procToBoole (p : Core.Procedure) : BuildM BCmd := do
  addFreeVars #[ppId p.header.name]
  let name := ann (ppId p.header.name)
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange := ann none
  let (inputBindings, inputNames) ← mkMonoInputs p.header.inputs
  let (outputDecls?, outputNames) ← mkMonoOutputs p.header.outputs
  let outputs := ann outputDecls?
  let (specElts, body) ← withScope do
    addBoundVars outputNames (reverse? := false)
    addBoundVars inputNames (reverse? := false)
    let specElts ← mkSpecElts p.spec
    let stmts ← p.body.mapM stmtToBoole
    let body := BooleDDM.Block.block default (ann stmts.toArray)
    pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.command_procedure default name typeArgs inputBindings outputs spec (ann (some body)))

private def funcToBoole (f : Core.Function) (decreases? : Option (List CoreExpr) := none) :
    BuildM BCmd := do
  addFreeVars #[ppId f.name]
  let name := ann (ppId f.name)
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange := ann none
  let (inputBindings, inputNames) ← mkMonoInputs f.inputs
  let outputTy ← coreMonoTyToBoole f.output
  let (body?, specElts) ← withScope do
    addBoundVars inputNames (reverse? := false)
    let body? ← match f.body with
      | some b => pure (some (← exprToBoole b))
      | none => pure none
    let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
    match decreases? with
    | some (d :: _) =>
      let _d' ← exprToBoole d
      pure ()  -- TODO: decreases in SpecElt
    | _ => pure ()
    for c in f.preconditions do
      let e ← exprToBoole c.expr
      elts := elts.push (.requires_spec default noLabel (ann none) e)
    for a in f.axioms do
      let e ← exprToBoole a
      elts := elts.push (.ensures_spec default noLabel (ann none) e)
    pure (body?, elts)
  match body? with
  | some body =>
    pure (.command_fndef default name typeArgs inputBindings outputTy (ann specElts) body (ann none))
  | none =>
    pure (.command_fndecl default name typeArgs inputBindings outputTy)

private def typeConsToBoole (tc : Core.TypeDecl) : BuildM BCmd := do
  match tc with
  | .con tcons =>
    addFreeVars #[tcons.name]
    let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if tcons.params.isEmpty then
        ann none
      else
        let bindings := tcons.params.toArray.map fun paramName =>
          BooleDDM.Binding.mkBinding default (ann paramName) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    pure (.command_typedecl default (ann tcons.name) args)
  | .syn ts =>
    addFreeVars #[ts.name]
    let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if ts.typeArgs.isEmpty then
        ann none
      else
        let bindings := ts.typeArgs.toArray.map fun param =>
          BooleDDM.Binding.mkBinding default (ann param) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    let rhs ← coreMonoTyToBoole ts.type
    pure (.command_typesynonym default (ann ts.name) args (ann none) rhs)
  | .data datatypes => do
    let dtNames := datatypes.toArray.map (·.name)
    addFreeVars dtNames
    for dt in datatypes do
      for c in dt.constrs do
        let constrName := c.name.name
        let testerName := c.testerName
        let destructorNames := c.args.toArray.map (fun (id, _) => id.name)
        addFreeVars (#[constrName, testerName] ++ destructorNames)
    let decls ← datatypes.toArray.mapM fun dt => do
      let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
        if dt.typeArgs.isEmpty then
          ann none
        else
          let bindings := dt.typeArgs.toArray.map fun param =>
            BooleDDM.Binding.mkBinding default (ann param) (BooleDDM.TypeP.type default)
          ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
      let constrs ← dt.constrs.toArray.mapM fun c => do
        let constrArgs ←
          if c.args.isEmpty then
            pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
          else do
            let bindings ← c.args.toArray.mapM fun (id, ty) => do
              let ty' ← coreMonoTyToBoole ty
              pure (BooleDDM.Binding.mkBinding default (ann id.name) (BooleDDM.TypeP.expr ty'))
            pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann c.name.name) constrArgs)
      let constrList :=
        if constrs.isEmpty then
          BooleDDM.ConstructorList.constructorListAtom default
            (BooleDDM.Constructor.constructor_mk default (ann "") (ann none))
        else
          constrs[1:].foldl
            (fun acc c => BooleDDM.ConstructorList.constructorListPush default acc c)
            (BooleDDM.ConstructorList.constructorListAtom default constrs[0]!)
      pure (BooleDDM.DatatypeDecl.datatype_decl default (ann dt.name) args constrList)
    pure (.command_datatypes default (ann decls))

private def axiomToBoole (a : Core.Axiom) : BuildM BCmd := do
  let e ← exprToBoole a.e
  pure (.command_axiom default (someLabel a.name) e)

private def varDeclToBoole (name : CoreIdent) (ty : LTy)
    (_e : Imperative.ExprOrNondet Expression) : BuildM BCmd := do
  let nameStr := ppId name
  addFreeVars #[nameStr]
  let ty' ← coreTyToBoole ty
  let bind := BooleDDM.Bind.bind_mk default (ann nameStr) (ann none) ty'
  pure (.command_var default bind)

private def distinctToBoole (lbl : CoreIdent) (es : List CoreExpr) : BuildM BCmd := do
  let es' ← es.toArray.mapM exprToBoole
  pure (.command_distinct default (someLabel (ppId lbl)) (ann es'))

def declToBoole (fnDecMap : Std.HashMap String (List CoreExpr))
    (d : Core.Decl) : BuildM BCmd := do
  match d with
  | .proc p _ => procToBoole p
  | .func f _ => funcToBoole f (fnDecMap.get? (ppId f.name))
  | .recFuncBlock fs _ => do
    for f in fs do addFreeVars #[ppId f.name]
    let cmds ← fs.mapM fun f => funcToBoole f (fnDecMap.get? (ppId f.name))
    match cmds with
    | [] => throw "empty recursive function block"
    | [c] => pure c
    | _ => pure cmds.head!
  | .type t _ => typeConsToBoole t
  | .ax a _ => axiomToBoole a
  | .var name ty e _ => varDeclToBoole name ty e
  | .distinct lbl es _ => distinctToBoole lbl es

/-! ## Top-level: Core.Program → Boole text -/

def renderBooleProgram
    (result : ToCore.ProgramLoweringResult)
    (preludeText? : Option String := none) :
    IO (Except String String) := do
  let preludeResult ←
    match preludeText? with
    | some text => loadPrelude text
    | none => pure (.ok (#[], #[]))
  match preludeResult with
  | .error e => pure (.error e)
  | .ok (preludeOps, preludeNames) =>
    let initCtx := (emptyCtx).addGlobalFreeVars preludeNames
    let computation : BuildM (Array Strata.Operation) := do
      let cmds ← result.program.decls.mapM (declToBoole result.fnDecMap)
      pure (cmds.toArray.map (·.toAst))
    match computation.run initCtx with
    | .ok (ops, _ctx) =>
      let pgm := mkProgram preludeOps ops
      pure (.ok (programToString pgm))
    | .error e => pure (.error e)

end VerusLean.Boole.CoreToBoole
