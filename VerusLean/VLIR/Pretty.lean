import VerusLean.VLIR.ToCore

namespace VerusLean

namespace ToCore

open Core
open Lambda

/-! ## Strata concrete-syntax pretty-printer (temp) -/

inductive OutputDialect where
  | core
  | boole
deriving DecidableEq, Repr

namespace Pretty

private def joinRefs (xss : List (List String)) : List String :=
  (xss.foldr (· ++ ·) []).eraseDups

private def exprOpRefsBy (keep : String → Bool) (e : CoreExpr) : List String :=
  ((Lambda.LExpr.getOps e).map CoreIdent.toPretty |>.filter keep).eraseDups

private def collectRefsFromChecks
    (exprRefs : CoreExpr → List String)
    (checks : ListMap CoreLabel Core.Procedure.Check) : List String :=
  joinRefs <| checks.values.map (fun c => exprRefs c.expr)

private partial def stmtRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String) :
    Core.Statement → List String
  | .cmd (.cmd (.init _ _ e _)) => (e.map exprRefs).getD []
  | .cmd (.cmd (.set _ e _)) => exprRefs e
  | .cmd (.cmd (.havoc _ _)) => []
  | .cmd (.cmd (.assert _ e _)) => exprRefs e
  | .cmd (.cmd (.assume _ e _)) => exprRefs e
  | .cmd (.cmd (.cover _ e _)) => exprRefs e
  | .cmd (.call _ f args _) =>
    joinRefs [callNameRefs f, joinRefs <| args.map exprRefs]
  | .block _ ss _ => joinRefs <| ss.map (stmtRefsBy exprRefs callNameRefs)
  | .ite cond t e _ =>
    joinRefs [exprRefs cond, joinRefs (t.map (stmtRefsBy exprRefs callNameRefs)), joinRefs (e.map (stmtRefsBy exprRefs callNameRefs))]
  | .loop guard measure invariant body _ =>
    let measureRefs := match measure with | some m => exprRefs m | none => []
    let invariantRefs := joinRefs <| invariant.map exprRefs
    joinRefs [exprRefs guard, measureRefs, invariantRefs, joinRefs (body.map (stmtRefsBy exprRefs callNameRefs))]
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

private def stmtsRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String)
    (ss : List Core.Statement) : List String :=
  joinRefs <| ss.map (stmtRefsBy exprRefs callNameRefs)

private def declRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String) :
    Core.Decl → List String
  | .func f _ => (f.body.map exprRefs).getD []
  | .recFuncBlock fs _ => joinRefs <| fs.map (fun f => (f.body.map exprRefs).getD [])
  | .proc p _ =>
    joinRefs [collectRefsFromChecks exprRefs p.spec.preconditions,
      collectRefsFromChecks exprRefs p.spec.postconditions,
      stmtsRefsBy exprRefs callNameRefs p.body]
  | .var _ _ e _ => (e.map exprRefs).getD []
  | .ax a _ => exprRefs a.e
  | .distinct _ es _ => joinRefs <| es.map exprRefs
  | .type _ _ => []

inductive PreparedStmt where
  | init (name : String) (ty : LTy) (rhs : Option CoreExpr)
  | set (name : String) (rhs : CoreExpr)
  | havoc (name : String)
  | assert (label : String) (e : CoreExpr)
  | assume (label : String) (e : CoreExpr)
  | cover (label : String) (e : CoreExpr)
  | call (lhs : List String) (pname : String) (args : List CoreExpr)
  | block (label : String) (body : List PreparedStmt)
  | ite (cond : CoreExpr) (thenBody : List PreparedStmt) (elseBody : List PreparedStmt)
  | loop (guard : CoreExpr) (measure : Option CoreExpr) (invs : List CoreExpr) (body : List PreparedStmt)
  | forLoop
      (loopVarName : String)
      (loopTy : LTy)
      (startExpr : CoreExpr)
      (limitExpr : CoreExpr)
      (measure : Option CoreExpr)
      (invs : List CoreExpr)
      (body : List PreparedStmt)
  | exit (label : Option String)
  | returnExpr (e : CoreExpr)
  | returnUnit
  | unsupportedFuncDecl
  | unsupportedTypeDecl
deriving Inhabited, Repr

structure PreparedProc where
  proc : Core.Procedure
  body : List PreparedStmt

structure PreparedFunction where
  func : Core.Function
  decreases? : Option (List CoreExpr)

inductive PreparedDecl where
  | proc (p : PreparedProc)
  | func (f : PreparedFunction)
  | recFuncBlock (fs : List PreparedFunction)
  | decl (d : Core.Decl)

structure PreparedProgram where
  decls : List PreparedDecl

private def ppCoreIdent (id : CoreIdent) : String :=
  -- Core AST identifiers are already normalized at construction sites.
  -- Re-sanitizing here can corrupt builtins (e.g. `Int.Sub` -> `Int_Sub`).
  CoreIdent.toPretty id

private def collectCoreApps : CoreExpr → CoreExpr × List CoreExpr
  | .app _ fn arg =>
    let (h, args) := collectCoreApps fn
    (h, args ++ [arg])
  | e => (e, [])

private def exprFVarName? : CoreExpr → Option String
  | .fvar _ id _ => some (ppCoreIdent id)
  | _ => none

private def exprHeadName? (e : CoreExpr) : Option String :=
  let (head, _) := collectCoreApps e
  match head with
  | .op _ id _ => some (ppCoreIdent id)
  | .fvar _ id _ => some (ppCoreIdent id)
  | _ => none

private def isTupleUnitCtorExpr (e : CoreExpr) : Bool :=
  match exprHeadName? e with
  | some "Tuple_ctor_0" => true
  | _ => false

private def isTrueExpr : CoreExpr → Bool
  | .boolConst _ true => true
  | _ => false

private def stmtSet? : Core.Statement → Option (String × CoreExpr)
  | .cmd (.cmd (.set name e _)) => some (ppCoreIdent name, e)
  | _ => none

private def stmtInitTy? : Core.Statement → Option (String × LTy)
  | .cmd (.cmd (.init name ty _ _)) => some (ppCoreIdent name, ty)
  | _ => none

private def exprRangeCtorArgs? (e : CoreExpr) : Option (CoreExpr × CoreExpr) :=
  let (head, args) := collectCoreApps e
  match head, args with
  | .op _ id _, [start, stop] =>
    if ppCoreIdent id == "Ops_Range_range_ctor" then some (start, stop) else none
  | _, _ => none

private def resolveAliasExpr (aliases : Std.HashMap String CoreExpr) (e : CoreExpr) : CoreExpr :=
  let rec go (fuel : Nat) (curr : CoreExpr) : CoreExpr :=
    match fuel with
    | 0 => curr
    | fuel + 1 =>
      match exprFVarName? curr with
      | some name =>
        match aliases.get? name with
        | some next => go fuel next
        | none => curr
      | none => curr
  go 32 e

private def loopIndexAsIntExpr (loopVarName : String) (ty : LTy) : CoreExpr :=
  let loopVar := LExpr.fvar () (CoreIdent.unres loopVarName) none
  match ty with
  | .forAll _ (.bitvec 64) =>
    LExpr.app () (LExpr.op () (CoreIdent.unres "bv64_to_int_u") none) loopVar
  | _ => loopVar

private def isBooleInternalTempName (name : String) : Bool :=
  name.startsWith "tmp" || name.startsWith "VERUS_"

def indentString (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

private partial def collectVarTypes (ss : List Core.Statement) : Std.HashMap String LTy :=
  let rec go (acc : Std.HashMap String LTy) (rest : List Core.Statement) : Std.HashMap String LTy :=
    match rest with
    | [] => acc
    | s :: tail =>
      let acc :=
        match stmtInitTy? s with
        | some (name, ty) => acc.insert name ty
        | none => acc
      let acc :=
        match s with
        | .block _ body _ => go acc body
        | .ite _ thenBranch elseBranch _ => go (go acc thenBranch) elseBranch
        | .loop _ _ _ body _ => go acc body
        | _ => acc
      go acc tail
  go ∅ ss

private def isExitToLabel (lbl : String) : List Core.Statement → Bool
  | [.exit (some l) _] => l == lbl
  | _ => false

private def matchOptionSomeCond? (e : CoreExpr) : Option String := do
  let (head, args) := collectCoreApps e
  match head, args with
  | .op _ id _, [arg] =>
    let name := ppCoreIdent id
    if name.contains "Option_option..isOption_option_Some" then
      exprFVarName? arg
    else
      none
  | _, _ => none

private def exprGhostPeekNextArgName? (e : CoreExpr) : Option String := do
  let (head, args) := collectCoreApps e
  match head, args with
  | .op _ id _, [arg] =>
    if ppCoreIdent id == "Pervasive_ghost_peek_next" then
      exprFVarName? arg
    else
      none
  | _, _ => none

private def matchGhostCurrentExprIterName? (e : CoreExpr) : Option String := do
  match e with
  | .ite _ cond thenExpr elseExpr =>
    let (condHead, condArgs) := collectCoreApps cond
    let condIter ←
      match condHead, condArgs with
      | .op _ id _, [arg] =>
        if ppCoreIdent id == "Option_option..isOption_option_Some" then
          exprGhostPeekNextArgName? arg
        else
          none
      | _, _ => none
    let (thenHead, thenArgs) := collectCoreApps thenExpr
    let thenIter ←
      match thenHead, thenArgs with
      | .op _ id _, [arg] =>
        if ppCoreIdent id == "Option_option..Option_option_Some_0" then
          exprGhostPeekNextArgName? arg
        else
          none
      | _, _ => none
    let (elseHead, elseArgs) := collectCoreApps elseExpr
    match elseHead, elseArgs with
    | .op _ id _, [] =>
      if condIter == thenIter && ppCoreIdent id == "Pervasive_arbitrary" then
        some condIter
      else
        none
    | _, _ => none
  | _ => none

private partial def findGhostCurrentIterName? : CoreExpr → Option String
  | e =>
    match matchGhostCurrentExprIterName? e with
    | some iterName => some iterName
    | none =>
      match e with
      | .eq _ lhs rhs => findGhostCurrentIterName? lhs <|> findGhostCurrentIterName? rhs
      | .ite _ cond thenExpr elseExpr =>
        findGhostCurrentIterName? cond <|>
          findGhostCurrentIterName? thenExpr <|>
          findGhostCurrentIterName? elseExpr
      | .quant _ _ _ _ trig body => findGhostCurrentIterName? trig <|> findGhostCurrentIterName? body
      | .abs _ _ _ body => findGhostCurrentIterName? body
      | .app _ fn arg => findGhostCurrentIterName? fn <|> findGhostCurrentIterName? arg
      | _ => none

private partial def exprHasFVarNamed (name : String) : CoreExpr → Bool
  | .fvar _ id _ => ppCoreIdent id == name
  | .eq _ lhs rhs => exprHasFVarNamed name lhs || exprHasFVarNamed name rhs
  | .ite _ cond thenExpr elseExpr =>
    exprHasFVarNamed name cond ||
      exprHasFVarNamed name thenExpr ||
      exprHasFVarNamed name elseExpr
  | .quant _ _ _ _ trig body => exprHasFVarNamed name trig || exprHasFVarNamed name body
  | .abs _ _ _ body => exprHasFVarNamed name body
  | .app _ fn arg => exprHasFVarNamed name fn || exprHasFVarNamed name arg
  | _ => false

private partial def rewriteGhostCurrentExpr
    (ghostIterName : String)
    (loopVarName : String)
    (loopTy : LTy) : CoreExpr → CoreExpr
  | e =>
    if matchGhostCurrentExprIterName? e == some ghostIterName then
      loopIndexAsIntExpr loopVarName loopTy
    else
      match e with
      | .eq md lhs rhs =>
        .eq md
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy lhs)
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy rhs)
      | .ite md cond thenExpr elseExpr =>
        .ite md
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy cond)
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy thenExpr)
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy elseExpr)
      | .quant md q name ty trig body =>
        .quant md q name ty
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy trig)
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy body)
      | .abs md name ty body =>
        .abs md name ty (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy body)
      | .app md fn arg =>
        .app md
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy fn)
          (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy arg)
      | _ => e

private def matchOptionUnwrapSet? (optName : String) : Core.Statement → Option String
  | .cmd (.cmd (.set name e _)) =>
    let (head, args) := collectCoreApps e
    match head, args with
    | .op _ id _, [arg] =>
      let ctorName := ppCoreIdent id
      if ctorName.contains "Option_option..Option_option_Some_0" &&
          exprFVarName? arg == some optName then
        some (ppCoreIdent name)
      else
        none
    | _, _ => none
  | _ => none

private def isBooleGhostLoopInvariant (e : CoreExpr) : Bool :=
  match exprHeadName? e with
  | some name =>
    name == "Pervasive_exec_invariant" ||
    name == "Pervasive_ghost_invariant" ||
    name == "Pervasive_ghost_ensures"
  | none => false

private abbrev RecoveredBooleForLoop :=
  List Core.Statement × List Core.Statement × CoreExpr × CoreExpr ×
    String × LTy × Option CoreExpr × List CoreExpr ×
    List Core.Statement × Option String

private def matchBooleForLoop?
    (varTypes : Std.HashMap String LTy)
    (ss : List Core.Statement) : Option RecoveredBooleForLoop := do
  let rec collectPrefix
      (aliases : Std.HashMap String CoreExpr)
      (pref : List Core.Statement)
      (rest : List Core.Statement) :
      Option (Std.HashMap String CoreExpr × List Core.Statement × Core.Statement × List Core.Statement) :=
    match rest with
    | [] => none
    | s :: tail =>
      match stmtInitTy? s, stmtSet? s with
      | some _, _ =>
        collectPrefix aliases (pref.concat s) tail
      | none, some (name, rhs) =>
          let aliases := aliases.insert name (resolveAliasExpr aliases rhs)
          collectPrefix aliases (pref.concat s) tail
      | none, none => some (aliases, pref, s, tail)
  let (aliases, pref, candidate, tail) ← collectPrefix ∅ [] ss
  match candidate with
  | .block lbl [ .loop guard measure invs loopBody _ ] _ =>
    if !isTrueExpr guard then
      none
    else
      match loopBody with
      | .cmd (.call lhs pname args _) :: rest =>
        if lhs.length != 2 then
          none
        else if !(pname.toLower.contains "iterator" && pname.toLower.endsWith "next") then
          none
        else
          let optTmp := ppCoreIdent lhs[0]!
          let iterVar := ppCoreIdent lhs[1]!
          let iterArgOk : Bool :=
            match args with
            | [arg] => exprFVarName? arg == some iterVar
            | _ => false
          if !iterArgOk then
            none
          else
            let (optName, rest) :=
              match rest with
              | s :: rest =>
                match stmtSet? s with
                | some (name, rhs) =>
                  if exprFVarName? rhs == some optTmp then
                    (name, rest)
                  else
                    (optTmp, s :: rest)
                | none => (optTmp, s :: rest)
              | [] => (optTmp, [])
            match rest with
            | .ite cond thenBranch elseBranch _ :: .cmd (.cmd (.set loopVar loopNext _)) :: bodyRest =>
              let loopVarName := ppCoreIdent loopVar
              let loopNextName? := exprFVarName? loopNext
              let extractedNext? :=
                match thenBranch with
                | [unwrapSet, .cmd (.cmd (.set nextName nextExpr _))] => do
                  let unwrapTmp ← matchOptionUnwrapSet? optName unwrapSet
                  let forwardedTmp ← exprFVarName? nextExpr
                  if forwardedTmp == unwrapTmp then
                    some (ppCoreIdent nextName)
                  else
                    none
                | _ => none
              if matchOptionSomeCond? cond != some optName then
                none
              else if !isExitToLabel lbl elseBranch then
                none
              else if loopNextName? != extractedNext? then
                none
              else
                let rangeExpr ← aliases.get? iterVar
                let (startExpr, stopExpr) ← exprRangeCtorArgs? rangeExpr
                let loopTy := varTypes.getD loopVarName (LTy.forAll [] .int)
                let ghostIterName? :=
                  match measure.bind findGhostCurrentIterName? with
                  | some name => some name
                  | none => invs.findSome? findGhostCurrentIterName?
                some (pref, tail, startExpr, stopExpr, loopVarName, loopTy, measure, invs, bodyRest, ghostIterName?)
            | _ => none
      | _ => none
  | _ => none

private def keepRecoveredBoolePrefixStmt (loopVarName : String) : Core.Statement → Bool
  | s =>
    match stmtInitTy? s, stmtSet? s with
    | some (name, _), _ => !(isBooleInternalTempName name || name == loopVarName)
    | none, some (name, _) => !isBooleInternalTempName name
    | none, none => false

private def exprAllDeclRefs (e : CoreExpr) : List String :=
  exprOpRefsBy (fun _ => true) e

private def callAllDeclRefs (name : String) : List String := [name]

mutual
private partial def stmtRefsForBooleStmt
    (varTypes : Std.HashMap String LTy) : Core.Statement → List String
  | .cmd (.cmd (.init name _ e _)) =>
    match e with
    | some rhs =>
      if isBooleInternalTempName (ppCoreIdent name) && isTupleUnitCtorExpr rhs then
        []
      else
        exprAllDeclRefs rhs
    | none => []
  | .cmd (.cmd (.set name e _)) =>
    if isBooleInternalTempName (ppCoreIdent name) && isTupleUnitCtorExpr e then
      []
    else
      exprAllDeclRefs e
  | .cmd (.cmd (.havoc _ _)) => []
  | .cmd (.cmd (.assert _ e _)) => exprAllDeclRefs e
  | .cmd (.cmd (.assume _ e _)) => exprAllDeclRefs e
  | .cmd (.cmd (.cover _ e _)) => exprAllDeclRefs e
  | .cmd (.call _ f args _) =>
    joinRefs [callAllDeclRefs f, joinRefs <| args.map exprAllDeclRefs]
  | .block _ ss _ => stmtsRefsForBoole varTypes ss
  | .ite cond t e _ =>
    joinRefs [exprAllDeclRefs cond, stmtsRefsForBoole varTypes t, stmtsRefsForBoole varTypes e]
  | .loop guard measure invs body _ =>
    let measureRefs := match measure with | some m => exprAllDeclRefs m | none => []
    let invariantRefs := joinRefs <| invs.map exprAllDeclRefs
    joinRefs [exprAllDeclRefs guard, measureRefs, invariantRefs, stmtsRefsForBoole varTypes body]
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

private partial def stmtsRefsForBoole
    (varTypes : Std.HashMap String LTy)
    (ss : List Core.Statement) : List String :=
  match matchBooleForLoop? varTypes ss with
  | some info =>
    match info with
    | (prefixStmts, tail, startExpr, stopExpr, loopVarName, loopTy, measureOpt, invs, bodyRest, ghostIterNameOpt) =>
      let prefixRefs :=
        joinRefs <| (prefixStmts.filter (keepRecoveredBoolePrefixStmt loopVarName)).map (stmtRefsForBooleStmt varTypes)
      let measureRefs :=
        match measureOpt, ghostIterNameOpt with
        | some m, some ghostIterName =>
          exprAllDeclRefs (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy m)
        | some m, none => exprAllDeclRefs m
        | none, _ => []
      let invRefs :=
        joinRefs <| invs.filterMap (fun inv =>
          if isBooleGhostLoopInvariant inv then
            none
          else
            let rewritten :=
              match ghostIterNameOpt with
              | some ghostIterName =>
                rewriteGhostCurrentExpr ghostIterName loopVarName loopTy inv
              | none => inv
            match ghostIterNameOpt with
            | some ghostIterName =>
              if exprHasFVarNamed ghostIterName rewritten then none else some (exprAllDeclRefs rewritten)
            | none => some (exprAllDeclRefs rewritten))
      joinRefs [
        prefixRefs,
        exprAllDeclRefs startExpr,
        exprAllDeclRefs stopExpr,
        measureRefs,
        invRefs,
        stmtsRefsForBoole varTypes bodyRest,
        stmtsRefsForBoole varTypes tail
      ]
  | none =>
    match ss with
    | [] => []
    | s :: rest => joinRefs [stmtRefsForBooleStmt varTypes s, stmtsRefsForBoole varTypes rest]
end

private def declRefsForBoole : Core.Decl → List String
  | .proc p _ =>
    let varTypes := collectVarTypes p.body
    joinRefs [
      collectRefsFromChecks exprAllDeclRefs p.spec.preconditions,
      collectRefsFromChecks exprAllDeclRefs p.spec.postconditions,
      stmtsRefsForBoole varTypes p.body
    ]
  | d => declRefsBy exprAllDeclRefs callAllDeclRefs d

private def isBoolePrunableDeclName : String → Bool
  | "Tuple_ctor_0"
  | "Unit"
  | "Ops_Range_range"
  | "Option_option"
  | "Std_specs_range"
  | "Pervasive_exec_invariant"
  | "Std_specs_Core_iter_into_iter_spec"
  | "Pervasive_arbitrary"
  | "Iter_Traits_Iterator_Iterator_next" => true
  | name => name.startsWith "Pervasive_ghost_"

private def closeBooleDeclRefs (prunableDecls : List Core.Decl) (seed : List String) : List String :=
  let prunableRefs := prunableDecls.map (fun d => (declNameString d, declRefsForBoole d))
  let rec loop (fuel : Nat) (keep : List String) : List String :=
    match fuel with
    | 0 => keep
    | fuel + 1 =>
      let expanded :=
        prunableRefs.foldl (init := keep) (fun acc (name, refs) =>
          if keep.contains name then
            (acc ++ refs).eraseDups
          else
            acc)
      if expanded == keep then keep else loop fuel expanded
  loop prunableDecls.length seed.eraseDups

private partial def pruneBooleStmtArtifacts (ss : List Core.Statement) : List Core.Statement :=
  let rec go : List Core.Statement → List Core.Statement
    | [] => []
    | s :: rest =>
      let rest' := go rest
      let keepStmt :=
        match s with
        | .cmd (.cmd (.init name _ (some rhs) _)) =>
          !(isBooleInternalTempName (ppCoreIdent name) && isTupleUnitCtorExpr rhs)
        | .cmd (.cmd (.set name rhs _)) =>
          !(isBooleInternalTempName (ppCoreIdent name) && isTupleUnitCtorExpr rhs)
        | _ => true
      if keepStmt then
        let s' :=
          match s with
          | .block lbl body md => Imperative.Stmt.block lbl (go body) md
          | .ite cond t e md => Imperative.Stmt.ite cond (go t) (go e) md
          | .loop guard measure invs body md => Imperative.Stmt.loop guard measure invs (go body) md
          | _ => s
        s' :: rest'
      else
        rest'
  go ss

private def prepareBooleDecl : Core.Decl → Core.Decl
  | .proc p md => .proc { p with body := pruneBooleStmtArtifacts p.body } md
  | d => d

private def pruneUnreferencedBooleDecls (decls : List Core.Decl) : List Core.Decl :=
  let (prunableDecls, keptDecls) := decls.partition (fun d => isBoolePrunableDeclName (declNameString d))
  let seed := joinRefs <| keptDecls.map declRefsForBoole
  let keep := closeBooleDeclRefs prunableDecls seed
  decls.filter (fun d =>
    if isBoolePrunableDeclName (declNameString d) then keep.contains (declNameString d) else true)

private def prepareCoreProgramForOutputDialect (dialect : OutputDialect) (p : Core.Program) : Core.Program :=
  match dialect with
  | .core => p
  | .boole =>
    let decls := p.decls.map prepareBooleDecl
    { p with decls := pruneUnreferencedBooleDecls decls }

private def subOneExprForTy (loopTy : LTy) (e : CoreExpr) : CoreExpr :=
  let one :=
    match loopTy with
    | LTy.forAll _ (.bitvec w) => LExpr.bitvecConst () w (BitVec.ofInt w 1)
    | _ => LExpr.intConst () 1
  let subOp :=
    match loopTy with
    | LTy.forAll _ (.bitvec w) =>
      (bvByWidth w Core.bv1SubOp Core.bv8SubOp Core.bv16SubOp Core.bv32SubOp Core.bv64SubOp).getD Core.intSubOp
    | _ => Core.intSubOp
  LExpr.app () (LExpr.app () subOp e) one

mutual
private partial def prepareStmtListForOutputDialect
    (dialect : OutputDialect)
    (varTypes : Std.HashMap String LTy)
    (ss : List Core.Statement) : List PreparedStmt :=
  match ss with
  | [] => []
  | _ =>
    let recovered? :=
      match dialect with
      | .boole => prepareRecoveredBooleForLoop? dialect varTypes ss
      | .core => none
    match recovered? with
    | some (prefixStmts, loopStmt, rest) =>
      prefixStmts ++ [loopStmt] ++ prepareStmtListForOutputDialect dialect varTypes rest
    | none =>
      match ss with
      | [] => []
      | .cmd (.cmd (.set _name e _)) :: .cmd (.cmd (.assume "__return__" _ _)) :: rest =>
        .returnExpr e :: prepareStmtListForOutputDialect dialect varTypes rest
      | .cmd (.cmd (.assume "__return__" _ _)) :: rest =>
        .returnUnit :: prepareStmtListForOutputDialect dialect varTypes rest
      | s :: rest =>
        prepareStmtForOutputDialect dialect varTypes s :: prepareStmtListForOutputDialect dialect varTypes rest

private partial def prepareStmtForOutputDialect
    (dialect : OutputDialect)
    (varTypes : Std.HashMap String LTy) : Core.Statement → PreparedStmt
  | .cmd (.cmd (.init name ty e _)) => .init (CoreIdent.toPretty name) ty e
  | .cmd (.cmd (.set name e _)) => .set (CoreIdent.toPretty name) e
  | .cmd (.cmd (.havoc name _)) => .havoc (CoreIdent.toPretty name)
  | .cmd (.cmd (.assert label e _)) => .assert label e
  | .cmd (.cmd (.assume "__return__" _ _)) => .returnUnit
  | .cmd (.cmd (.assume label e _)) => .assume label e
  | .cmd (.cmd (.cover label e _)) => .cover label e
  | .cmd (.call lhs pname args _) => .call (lhs.map CoreIdent.toPretty) pname args
  | .block lbl ss _ => .block lbl (prepareStmtListForOutputDialect dialect varTypes ss)
  | .ite cond t e _ => .ite cond (prepareStmtListForOutputDialect dialect varTypes t) (prepareStmtListForOutputDialect dialect varTypes e)
  | .loop guard measure invs body _ => .loop guard measure invs (prepareStmtListForOutputDialect dialect varTypes body)
  | .exit lbl _ => .exit lbl
  | .funcDecl _ _ => .unsupportedFuncDecl
  | .typeDecl _ _ => .unsupportedTypeDecl

private partial def prepareRecoveredBooleForLoop?
    (dialect : OutputDialect)
    (varTypes : Std.HashMap String LTy)
    (ss : List Core.Statement) : Option (List PreparedStmt × PreparedStmt × List Core.Statement) := do
  let info ← matchBooleForLoop? varTypes ss
  match info with
  | (prefixStmts, tail, startExpr, stopExpr, loopVarName, loopTy, measureOpt, invs, bodyRest, ghostIterNameOpt) =>
    let prefixPrepared :=
      prepareStmtListForOutputDialect dialect varTypes
        (prefixStmts.filter (keepRecoveredBoolePrefixStmt loopVarName))
    let measurePrepared :=
      match measureOpt with
      | some m =>
        match ghostIterNameOpt with
        | some ghostIterName => some (rewriteGhostCurrentExpr ghostIterName loopVarName loopTy m)
        | none => some m
      | none => none
    let invsPrepared := invs.filterMap (fun inv =>
      if isBooleGhostLoopInvariant inv then
        none
      else
        let rewritten :=
          match ghostIterNameOpt with
          | some ghostIterName => rewriteGhostCurrentExpr ghostIterName loopVarName loopTy inv
          | none => inv
        match ghostIterNameOpt with
        | some ghostIterName =>
          if exprHasFVarNamed ghostIterName rewritten then none else some rewritten
        | none => some rewritten)
    let limitExpr := subOneExprForTy loopTy stopExpr
    let bodyPrepared := prepareStmtListForOutputDialect dialect varTypes bodyRest
    some (prefixPrepared, .forLoop loopVarName loopTy startExpr limitExpr measurePrepared invsPrepared bodyPrepared, tail)
end

private def filterVisibleModifies (p : Core.Procedure) : Core.Procedure :=
  let varTypes := collectVarTypes p.body
  let visibleVars : Std.HashSet String :=
    let fromSig :=
      (p.header.inputs ++ p.header.outputs).foldl (init := ({} : Std.HashSet String))
        (fun acc (id, _) => acc.insert (CoreIdent.toPretty id))
    varTypes.fold (init := fromSig) (fun acc name _ => acc.insert name)
  let modifies := p.spec.modifies.filter (fun v => visibleVars.contains (CoreIdent.toPretty v))
  { p with spec := { p.spec with modifies := modifies } }

private def prepareDeclForOutputDialect
    (dialect : OutputDialect)
    (fnDecMap : Std.HashMap String (List CoreExpr)) : Core.Decl → PreparedDecl
  | .proc p _ =>
    let p :=
      match dialect with
      | .boole => filterVisibleModifies p
      | .core => p
    .proc { proc := p, body := prepareStmtListForOutputDialect dialect (collectVarTypes p.body) p.body }
  | .func f _ =>
    .func { func := f, decreases? := fnDecMap.get? (CoreIdent.toPretty f.name) }
  | .recFuncBlock fs _ =>
    .recFuncBlock <| fs.map (fun f => { func := f, decreases? := fnDecMap.get? (CoreIdent.toPretty f.name) })
  | d => .decl d

def prepareProgramForOutputDialect
    (dialect : OutputDialect)
    (p : Core.Program)
    (fnDecMap : Std.HashMap String (List CoreExpr) := ∅) : PreparedProgram :=
  let p := prepareCoreProgramForOutputDialect dialect p
  { decls := p.decls.map (prepareDeclForOutputDialect dialect fnDecMap) }

mutual
partial def monoTyToString : LMonoTy → String
  | .tcons "bool" [] => "bool"
  | .tcons "int" [] => "int"
  | .tcons "string" [] => "string"
  | .bitvec n => s!"bv{n}"
  | .ftvar n => n
  | .tcons "arrow" [arg, res] =>
    s!"{monoTyArgToString arg} -> {monoTyToString res}"
  | .tcons name [] => name
  | .tcons name args =>
    let argsStr := String.intercalate " " (args.map monoTyArgToString)
    s!"{name} {argsStr}"

partial def monoTyArgToString : LMonoTy → String
  | t@(.tcons _ (_ :: _)) => s!"({monoTyToString t})"
  | t => monoTyToString t
end

def tyToString (ty : LTy) : String :=
  match ty with
  | .forAll _ mty => monoTyToString mty

partial def exprToString (e : CoreExpr) : String :=
  exprToStringWithBound [] e
where
  constToString : LConst → String
  | .intConst i => toString i
  | .boolConst b => if b then "true" else "false"
  | .strConst s => s!"\"{s}\""
  | .realConst r => toString r
  | .bitvecConst n b => "bv{" ++ toString n ++ "}(" ++ toString b.toNat ++ ")"

  callString (name : String) (args : List String) : String :=
    s!"{name}({String.intercalate ", " args})"

  bvUnaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "Not" => some "~"
      | some "Neg" => some "-"
      | _ => none
    else
      none

  bvBinaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "Add" => some "+"
      | some "Sub" => some "-"
      | some "Mul" => some "*"
      | some "And" => some "&"
      | some "Or" => some "|"
      | some "Xor" => some "^"
      | some "Shl" => some "<<"
      | some "UShr" => some ">>"
      | some "SShr" => some ">>s"
      | some "UDiv" => some "div"
      | some "UMod" => some "mod"
      | some "SDiv" => some "sdiv"
      | some "SMod" => some "smod"
      | some "ULt" => some "<"
      | some "ULe" => some "<="
      | some "UGt" => some ">"
      | some "UGe" => some ">="
      | some "SLt" => some "<s"
      | some "SLe" => some "<=s"
      | some "SGt" => some ">s"
      | some "SGe" => some ">=s"
      | _ => none
    else
      none

  getBound? (bound : List String) (idx : Nat) : Option String :=
    let rec go (i : Nat) (rest : List String) : Option String :=
      match rest with
      | [] => none
      | x :: xs => if i == idx then some x else go (i + 1) xs
    go 0 bound

  collectQuantChain
      (k : Lambda.QuantifierKind)
      (boundAcc : List String)
      (e : CoreExpr) :
      (List (String × Option String) × List String × CoreExpr × CoreExpr) :=
    let rec go (boundNow : List String) (acc : List (String × Option String))
        (lastTrig : CoreExpr) (cur : CoreExpr) :
        (List (String × Option String) × List String × CoreExpr × CoreExpr) :=
      match cur with
      | .quant _ k' name ty trig body =>
        if k' == k then
          let binderName := if name.isEmpty then s!"x{boundNow.length}" else name
          let tyStr := ty.map (fun mty => tyToString (.forAll [] mty))
          go (binderName :: boundNow) (acc ++ [(binderName, tyStr)]) trig body
        else
          (acc, boundNow, lastTrig, cur)
      | _ => (acc, boundNow, lastTrig, cur)
    go boundAcc [] (LExpr.noTrigger ()) e

  decodeTriggerTree (bound : List String) (e : CoreExpr) : List String :=
    match e with
    | .bvar _ 0 => []
    | .app _ (.app _ (.op _ name _) arg) rest =>
      match name.name with
      | "TriggerGroup.addTrigger" =>
        exprToStringWithBound bound arg :: decodeTriggerTree bound rest
      | "Triggers.addGroup" =>
        decodeTriggerTree bound arg ++ decodeTriggerTree bound rest
      | _ => []
    | .op _ name _ =>
      if name.name == "TriggerGroup.empty" || name.name == "Triggers.empty"
      then []
      else []
    | _ => []

  triggerGroupsStr (bound : List String) (trigExpr : CoreExpr) : String :=
    match trigExpr with
    | .bvar _ 0 => ""
    | _ =>
      let exprs := decodeTriggerTree bound trigExpr
      if exprs.isEmpty then ""
      else
        s!" \{ {String.intercalate ", " exprs} }\n  "

  exprToStringWithBound (bound : List String) (e : CoreExpr) : String :=
    match e with
    | .const _ c => constToString c
    | .fvar _ id _ => ppCoreIdent id
    | .op _ id _ => ppCoreIdent id
    | .bvar _ idx =>
      match getBound? bound idx with
      | some name => name
      | none => s!"_b{idx}"
    | .eq _ a b => s!"({exprToStringWithBound bound a} == {exprToStringWithBound bound b})"
    | .ite _ c t f =>
      s!"(if {exprToStringWithBound bound c} then {exprToStringWithBound bound t} else {exprToStringWithBound bound f})"
    | .quant _ k _ _ _ _ =>
      let kw := match k with
        | .all => "forall"
        | .exist => "exists"
      let (binders, bound', trigExpr, body) := collectQuantChain k bound e
      let binderStrs := binders.map (fun (name, tyStr) =>
        match tyStr with
        | some ts => s!"{name}: {ts}"
        | none => name)
      let trigStr := triggerGroupsStr bound' trigExpr
      s!"{kw} {String.intercalate ", " binderStrs} ::{trigStr} {exprToStringWithBound bound' body}"
    | .abs _ _ _ _ =>
      "Unsupported.lambda"
    | .app _ _ _ =>
      let (head, args) := collectCoreApps e
      match head, args with
      | .op _ id _, [a] =>
        match ppCoreIdent id with
        | "Bool.Not" => s!"(!{exprToStringWithBound bound a})"
        | "Int.Neg" => s!"(-{exprToStringWithBound bound a})"
        | op =>
          match bvUnaryOp? op with
          | some sym => s!"({sym}{exprToStringWithBound bound a})"
          | none => callString op [exprToStringWithBound bound a]
      | .op _ id _, [a, b] =>
        let op := ppCoreIdent id
        let lhs := exprToStringWithBound bound a
        let rhs := exprToStringWithBound bound b
        match op with
        | "Map.Select" => s!"({lhs}[{rhs}])"
        | "select" => s!"({lhs}[{rhs}])"
        | "Int.Add" => s!"({lhs} + {rhs})"
        | "Int.Sub" => s!"({lhs} - {rhs})"
        | "Int.Mul" => s!"({lhs} * {rhs})"
        | "Int.Div" => s!"({lhs} div {rhs})"
        | "Int.Mod" => s!"({lhs} mod {rhs})"
        | "Int.Lt" => s!"({lhs} < {rhs})"
        | "Int.Le" => s!"({lhs} <= {rhs})"
        | "Int.Gt" => s!"({lhs} > {rhs})"
        | "Int.Ge" => s!"({lhs} >= {rhs})"
        | "Bool.And" => s!"({lhs} && {rhs})"
        | "Bool.Or" => s!"({lhs} || {rhs})"
        | "Bool.Implies" => s!"({lhs} ==> {rhs})"
        | "Bool.Equiv" => s!"({lhs} == {rhs})"
        | _ =>
          match bvBinaryOp? op with
          | some sym => s!"({lhs} {sym} {rhs})"
          | none => callString op [lhs, rhs]
      | .op _ id _, [a, b, c] =>
        let op := ppCoreIdent id
        let lhs := exprToStringWithBound bound a
        let idx := exprToStringWithBound bound b
        let val := exprToStringWithBound bound c
        match op with
        | "Map.Update" => s!"({lhs}[{idx} := {val}])"
        | "update" => s!"({lhs}[{idx} := {val}])"
        | _ => callString op [lhs, idx, val]
      | .op _ id _, _ =>
        callString (ppCoreIdent id) (args.map (exprToStringWithBound bound))
      | .fvar _ id _, _ =>
        callString (ppCoreIdent id) (args.map (exprToStringWithBound bound))
      | .bvar _ _, _ =>
        callString (exprToStringWithBound bound head) (args.map (exprToStringWithBound bound))
      | _, _ =>
        "Unsupported.expr"

mutual
partial def stmtsToLines
    (indent : Nat)
    (ss : List PreparedStmt) : List String :=
  match ss with
  | [] => []
  | s :: rest => stmtToLines indent s ++ stmtsToLines indent rest

partial def stmtToLines
    (indent : Nat)
    (s : PreparedStmt) : List String :=
  let pad := indentString indent
  match s with
  | .init n ty e =>
    match e with
    | none =>
      [s!"{pad}var {n} : {tyToString ty};"]
    | some rhs =>
      [s!"{pad}var {n} : {tyToString ty} := {exprToString rhs};"]
  | .set name e =>
    [s!"{pad}{name} := {exprToString e};"]
  | .havoc name =>
    [s!"{pad}havoc {name};"]
  | .assert label e =>
    if label.isEmpty then
      [s!"{pad}assert {exprToString e};"]
    else
      [s!"{pad}assert [{label}]: {exprToString e};"]
  | .assume label e =>
    if label.isEmpty then
      [s!"{pad}assume {exprToString e};"]
    else
      [s!"{pad}assume [{label}]: {exprToString e};"]
  | .cover label e =>
    if label.isEmpty then
      [s!"{pad}cover {exprToString e};"]
    else
      [s!"{pad}cover [{label}]: {exprToString e};"]
  | .call lhs pname args =>
    let lhsStr :=
      if lhs.isEmpty then ""
      else s!"{String.intercalate ", " lhs} := "
    let argsStr := String.intercalate ", " (args.map exprToString)
    [s!"{pad}call {lhsStr}{pname}({argsStr});"]
  | .block lbl ss =>
    let body := stmtsToLines (indent + 1) ss
    if lbl.isEmpty then
      [pad ++ "{"] ++ body ++ [pad ++ "}"]
    else
      [s!"{pad}{lbl}:", pad ++ "{"] ++ body ++ [pad ++ "}"]
  | .ite cond t e =>
    let head := s!"{pad}if ({exprToString cond}) " ++ "{"
    let thenLines := stmtsToLines (indent + 1) t
    if e.isEmpty then
      [head] ++ thenLines ++ [pad ++ "}"]
    else
      let elseLines := stmtsToLines (indent + 1) e
      [head] ++ thenLines ++ [pad ++ "} else {"] ++ elseLines ++ [pad ++ "}"]
  | .loop guard measure invs body =>
    let measureLine := match measure with
      | some m => [s!"{pad}  decreases {exprToString m}"]
      | none => []
    let invLine := invs.map (fun i => s!"{pad}  invariant {exprToString i}")
    let head := s!"{pad}while ({exprToString guard})"
    let bodyLines := stmtsToLines (indent + 1) body
    [head] ++ measureLine ++ invLine ++ [pad ++ "{"] ++ bodyLines ++ [pad ++ "}"]
  | .forLoop loopVarName loopTy startExpr limitExpr measure invs body =>
    let header := s!"{pad}for {loopVarName} : {tyToString loopTy} := {exprToString startExpr} to {exprToString limitExpr}"
    let invLines := invs.map (fun inv => s!"{pad}  invariant {exprToString inv}")
    let measureLines :=
      match measure with
      | some m => [s!"{pad}  // decreases ({exprToString m})"]
      | none => []
    let bodyLines := stmtsToLines (indent + 1) body
    [header] ++ invLines ++ measureLines ++ [pad ++ "{"] ++ bodyLines ++ [pad ++ "}"]
  | .exit lbl =>
    match lbl with
      | some l => [s!"{pad}exit {l};"]
      | none => [s!"{pad}exit;"]
  | .returnExpr e =>
    [s!"{pad}// return {exprToString e};"]
  | .returnUnit =>
    [s!"{pad}// return;"]
  | .unsupportedFuncDecl =>
    [s!"{pad}/* unsupported: statement-level function declaration */"]
  | .unsupportedTypeDecl =>
    [s!"{pad}/* unsupported: statement-level type declaration */"]
end

def typeArgsToString (args : List String) : String :=
  if args.isEmpty then "" else s!"<{String.intercalate ", " args}>"

def typeParamsToString (num : Nat) : String :=
  if num == 0 then
    ""
  else
    let names := (List.range num).map (fun i => s!"T{i}")
    let binds := names.map (fun n => s!"{n}: Type")
    s!" ({String.intercalate ", " binds})"

def datatypeTypeArgsToString (args : List String) : String :=
  if args.isEmpty then
    "()"
  else
    let binds := args.map (fun n => s!"{sanitizeIdent n}: Type")
    "(" ++ String.intercalate ", " binds ++ ")"

def datatypeConstrToString (c : LConstr Visibility) : String :=
  let fields :=
    c.args.map (fun (field, ty) =>
      s!"{CoreIdent.toPretty field}: {tyToString (.forAll [] ty)}")
  s!"{CoreIdent.toPretty c.name}({String.intercalate ", " fields})"

def datatypeDeclToString (d : LDatatype Visibility) : String :=
  let ctors := String.intercalate ", " (d.constrs.map datatypeConstrToString)
  "datatype " ++ d.name ++ " " ++ datatypeTypeArgsToString d.typeArgs ++ " { " ++ ctors ++ " };"

def procToString (pp : PreparedProc) : String :=
  let p := pp.proc
  let inputs := sigToString p.header.inputs
  let outputs := sigToString p.header.outputs
  let header :=
    s!"procedure {CoreIdent.toPretty p.header.name}{typeArgsToString p.header.typeArgs}({inputs}) returns ({outputs})"
  let specLines :=
    (p.spec.modifies.map (fun v => s!"  modifies {CoreIdent.toPretty v};"))
    ++ (p.spec.preconditions.map (fun pair =>
        let c : Core.Procedure.Check := pair.snd
        s!"  requires ({exprToString c.expr});"))
    ++ (p.spec.postconditions.map (fun pair =>
        let c : Core.Procedure.Check := pair.snd
        s!"  ensures ({exprToString c.expr});"))
  let specBlock :=
    if specLines.isEmpty then
      []
    else
      ["spec {"] ++ specLines ++ ["}"]
  let bodyLines := stmtsToLines 1 pp.body
  let body := ["{"] ++ bodyLines ++ ["};"]
  String.intercalate "\n" ([header] ++ specBlock ++ body)
where
  sigToString (sig : @Lambda.LMonoTySignature Visibility) : String :=
    String.intercalate ", " (sig.map (fun (id, ty) =>
      s!"{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))

def funcToString
    (dialect : OutputDialect)
    (pf : PreparedFunction) : String :=
  let f := pf.func
  let recCasesIdx? :=
    if f.body.isSome then
      Strata.DL.Util.FuncAttr.findInlineIfConstr f.attr
    else
      none
  let inputs := String.intercalate ", " (f.inputs.zipIdx.map (fun ((id, ty), i) =>
    let ann := if recCasesIdx? == some i then "@[cases] " else ""
    s!"{ann}{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))
  let header := s!"function {CoreIdent.toPretty f.name}{typeArgsToString f.typeArgs}({inputs}): {tyToString (.forAll [] f.output)}"
  let decComment :=
    match dialect, pf.decreases? with
    | .boole, some exprs =>
      let exprsStr := String.intercalate ", " (exprs.map exprToString)
      s!"\n    // decreases ({exprsStr})"
    | _, _ => ""
  match f.body with
  | none => header ++ ";" ++ decComment
  | some body =>
    let bodyStr := exprToString body
    if decComment.isEmpty then
      String.intercalate "\n" [header ++ " {", "  " ++ bodyStr, "}"]
    else
      String.intercalate "\n" [header ++ decComment, "{", "  " ++ bodyStr, "}"]

private def recFuncBlockToString
    (dialect : OutputDialect)
    (fs : List PreparedFunction) : String :=
  match fs with
  | [] => ""
  | _ =>
    let rendered := fs.map (fun pf => funcToString dialect { pf with func := { pf.func with isRecursive := false } })
    "rec " ++ String.intercalate "\n" rendered ++ ";"

def declToString
    (dialect : OutputDialect)
    (d : PreparedDecl) : String :=
  match d with
  | .proc p => procToString p
  | .func pf =>
    if pf.func.isRecursive && pf.func.body.isSome then
      recFuncBlockToString dialect [pf]
    else
      funcToString dialect pf
  | .recFuncBlock fs => recFuncBlockToString dialect fs
  | .decl d =>
    match d with
    | .proc _ _ => "/* unexpected raw procedure decl in prepared printer */"
    | .func _ _ => "/* unexpected raw function decl in prepared printer */"
    | .recFuncBlock _ _ => "/* unexpected raw recursive function block in prepared printer */"
    | .type t _ =>
      match t with
      | .con c => s!"type {c.name}{typeParamsToString c.numargs};"
      | .syn s => s!"type {s.name} := {tyToString (.forAll [] s.type)};"
      | .data ds => String.intercalate "\n" (ds.map datatypeDeclToString)
    | .ax a _ => s!"axiom {CoreIdent.toPretty a.name}: {exprToString a.e};"
    | .var name ty e _ =>
      match e with
      | some rhs => s!"var {CoreIdent.toPretty name} : {tyToString ty} := {exprToString rhs};"
      | none => s!"var {CoreIdent.toPretty name} : {tyToString ty};"
    | .distinct lbl es _ =>
      let esStr := String.intercalate ", " (es.map exprToString)
      s!"distinct [{lbl}] {esStr};"

def programToString
    (p : PreparedProgram)
    (dialect : OutputDialect := .core) : String :=
  let decls :=
    p.decls.map (fun d => declToString dialect d)
      |>.filter (fun s => !s.isEmpty)
  let body := String.intercalate "\n\n" decls
  let header :=
    match dialect with
    | .core => "program Core;\n"
    | .boole => "program Boole;\n"
  if body.isEmpty then
    header
  else
    header ++ "\n" ++ body ++ "\n"

end Pretty

def declsToCoreString (decls : List Decl) : Except String String := do
  let (p, fnDecMap, _) ← declsToProgram decls
  let p := Pretty.prepareProgramForOutputDialect .core p fnDecMap
  return Pretty.programToString p

end ToCore

end VerusLean
