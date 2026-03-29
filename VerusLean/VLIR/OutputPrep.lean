import VerusLean.VLIR.ToCore

namespace VerusLean

namespace ToCore

open Core
open Lambda

inductive OutputDialect where
  | core
  | boole
deriving DecidableEq, Repr

namespace OutputPrep

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
  | typeDecl (t : Core.TypeDecl)
  | axiom (a : Core.Axiom)
  | var (name : CoreIdent) (ty : LTy) (rhs : Option CoreExpr)
  | distinct (lbl : CoreIdent) (es : List CoreExpr)

structure PreparedProgram where
  decls : List PreparedDecl

private def ppCoreIdent (id : CoreIdent) : String :=
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

private def pruneUnreferencedBooleDecls
    (prunableNames : Std.HashSet String)
    (decls : List Core.Decl) : List Core.Decl :=
  let (prunableDecls, keptDecls) := decls.partition (fun d => prunableNames.contains (declNameString d))
  let seed := joinRefs <| keptDecls.map declRefsForBoole
  let keep := closeBooleDeclRefs prunableDecls seed
  decls.filter (fun d =>
    if prunableNames.contains (declNameString d) then keep.contains (declNameString d) else true)

private def prepareCoreProgramForOutputDialect
    (dialect : OutputDialect)
    (p : Core.Program)
    (boolePrunableDeclNames : Std.HashSet String) : Core.Program :=
  match dialect with
  | .core => p
  | .boole =>
    let decls := p.decls.map prepareBooleDecl
    { p with decls := pruneUnreferencedBooleDecls boolePrunableDeclNames decls }

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
    (ss : List Core.Statement) : Except String (List PreparedStmt) := do
  match ss with
  | [] => return []
  | _ =>
    let recovered? ←
      match dialect with
      | .boole => prepareRecoveredBooleForLoop? dialect varTypes ss
      | .core =>
        pure (none : Option (List PreparedStmt × PreparedStmt × List Core.Statement))
    match recovered? with
    | some (prefixStmts, loopStmt, rest) =>
      return prefixStmts ++ [loopStmt] ++ (← prepareStmtListForOutputDialect dialect varTypes rest)
    | none =>
      match ss with
      | [] => return []
      | .cmd (.cmd (.set _name e _)) :: .cmd (.cmd (.assume "__return__" _ _)) :: rest =>
        return .returnExpr e :: (← prepareStmtListForOutputDialect dialect varTypes rest)
      | .cmd (.cmd (.assume "__return__" _ _)) :: rest =>
        return .returnUnit :: (← prepareStmtListForOutputDialect dialect varTypes rest)
      | s :: rest =>
        return (← prepareStmtForOutputDialect dialect varTypes s) ::
          (← prepareStmtListForOutputDialect dialect varTypes rest)

private partial def prepareStmtForOutputDialect
    (dialect : OutputDialect)
    (varTypes : Std.HashMap String LTy) : Core.Statement → Except String PreparedStmt
  | .cmd (.cmd (.init name ty e _)) => return .init (CoreIdent.toPretty name) ty e
  | .cmd (.cmd (.set name e _)) => return .set (CoreIdent.toPretty name) e
  | .cmd (.cmd (.havoc name _)) => return .havoc (CoreIdent.toPretty name)
  | .cmd (.cmd (.assert label e _)) => return .assert label e
  | .cmd (.cmd (.assume "__return__" _ _)) => return .returnUnit
  | .cmd (.cmd (.assume label e _)) => return .assume label e
  | .cmd (.cmd (.cover label e _)) => return .cover label e
  | .cmd (.call lhs pname args _) => return .call (lhs.map CoreIdent.toPretty) pname args
  | .block lbl ss _ => return .block lbl (← prepareStmtListForOutputDialect dialect varTypes ss)
  | .ite cond t e _ =>
    return .ite cond
      (← prepareStmtListForOutputDialect dialect varTypes t)
      (← prepareStmtListForOutputDialect dialect varTypes e)
  | .loop guard measure invs body _ =>
    return .loop guard measure invs (← prepareStmtListForOutputDialect dialect varTypes body)
  | .exit lbl _ => return .exit lbl
  | .funcDecl _ _ => throw "unexpected statement-level function declaration during output preparation"
  | .typeDecl _ _ => throw "unexpected statement-level type declaration during output preparation"

private partial def prepareRecoveredBooleForLoop?
    (dialect : OutputDialect)
    (varTypes : Std.HashMap String LTy)
    (ss : List Core.Statement) :
    Except String (Option (List PreparedStmt × PreparedStmt × List Core.Statement)) := do
  let info := matchBooleForLoop? varTypes ss
  match info with
  | some (prefixStmts, tail, startExpr, stopExpr, loopVarName, loopTy, measureOpt, invs, bodyRest, ghostIterNameOpt) =>
    let prefixPrepared :=
      ← prepareStmtListForOutputDialect dialect varTypes
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
    let bodyPrepared ← prepareStmtListForOutputDialect dialect varTypes bodyRest
    return some (prefixPrepared, .forLoop loopVarName loopTy startExpr limitExpr measurePrepared invsPrepared bodyPrepared, tail)
  | none => return none
end

private def filterVisibleModifies
    (p : Core.Procedure)
    (varTypes : Std.HashMap String LTy) : Core.Procedure :=
  let visibleVars : Std.HashSet String :=
    let fromSig :=
      (p.header.inputs ++ p.header.outputs).foldl (init := ({} : Std.HashSet String))
        (fun acc (id, _) => acc.insert (CoreIdent.toPretty id))
    varTypes.fold (init := fromSig) (fun acc name _ => acc.insert name)
  let modifies := p.spec.modifies.filter (fun v => visibleVars.contains (CoreIdent.toPretty v))
  { p with spec := { p.spec with modifies := modifies } }

private def prepareDeclForOutputDialect
    (dialect : OutputDialect)
    (fnDecMap : Std.HashMap String (List CoreExpr)) : Core.Decl → Except String PreparedDecl
  | .proc p _ =>
    let varTypes := collectVarTypes p.body
    let p :=
      match dialect with
      | .boole => filterVisibleModifies p varTypes
      | .core => p
    return .proc { proc := p, body := (← prepareStmtListForOutputDialect dialect varTypes p.body) }
  | .func f _ =>
    return .func { func := f, decreases? := fnDecMap.get? (CoreIdent.toPretty f.name) }
  | .recFuncBlock fs _ =>
    return .recFuncBlock <| fs.map (fun f => { func := f, decreases? := fnDecMap.get? (CoreIdent.toPretty f.name) })
  | .type t _ => return .typeDecl t
  | .ax a _ => return .axiom a
  | .var name ty e _ => return .var name ty e
  | .distinct lbl es _ => return .distinct lbl es

def prepareProgramForOutputDialect
    (dialect : OutputDialect)
    (p : Core.Program)
    (fnDecMap : Std.HashMap String (List CoreExpr) := ∅)
    (boolePrunableDeclNames : Std.HashSet String := ∅) : Except String PreparedProgram := do
  let p := prepareCoreProgramForOutputDialect dialect p boolePrunableDeclNames
  return { decls := ← p.decls.mapM (prepareDeclForOutputDialect dialect fnDecMap) }

end OutputPrep

end ToCore

end VerusLean
