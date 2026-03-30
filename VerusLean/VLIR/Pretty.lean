import VerusLean.VLIR.OutputPrep

namespace VerusLean

namespace ToCore

open Core
open Lambda

namespace Pretty

open OutputPrep

private def ppCoreIdent (id : CoreIdent) : String :=
  CoreIdent.toPretty id

def indentString (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

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

  fixedOpArity? (name : String) : Option Nat :=
    match name with
    | "Bool.Not"
    | "Int.Neg" => some 1
    | "Map.Select"
    | "Sequence.select"
    | "select"
    | "Int.Add"
    | "Int.Sub"
    | "Int.Mul"
    | "Int.Div"
    | "Int.Mod"
    | "Int.Lt"
    | "Int.Le"
    | "Int.Gt"
    | "Int.Ge"
    | "Bool.And"
    | "Bool.Or"
    | "Bool.Implies"
    | "Bool.Equiv" => some 2
    | "Map.Update"
    | "Sequence.update"
    | "update" => some 3
    | _ =>
      if name.startsWith "Bv" then
        match (name.splitOn ".").getLast? with
        | some "Not"
        | some "Neg" => some 1
        | some "Add"
        | some "Sub"
        | some "Mul"
        | some "And"
        | some "Or"
        | some "Xor"
        | some "Shl"
        | some "UShr"
        | some "SShr"
        | some "UDiv"
        | some "UMod"
        | some "SDiv"
        | some "SMod"
        | some "ULt"
        | some "ULe"
        | some "UGt"
        | some "UGe"
        | some "SLt"
        | some "SLe"
        | some "SGt"
        | some "SGe" => some 2
        | _ => none
      else
        none

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

  freshBinderName (base : String) (used : List String) : String :=
    if !used.contains base then
      base
    else
      let rec go (i : Nat) : String :=
        let cand := s!"{base}_{i}"
        if used.contains cand then go (i + 1) else cand
      go 1

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
          let rawName := if name.isEmpty then s!"x{boundNow.length}" else name
          let binderName := freshBinderName rawName boundNow
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
        " { " ++ String.intercalate ", " exprs ++ " }\n  "

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
      let rec collectCoreApps : CoreExpr → CoreExpr × List CoreExpr
        | .app _ fn arg =>
          let (h, args) := collectCoreApps fn
          (h, args ++ [arg])
        | e => (e, [])
      let (head, args) := collectCoreApps e
      let renderAppliedResult : String → List CoreExpr → String :=
        fun accPrefix restArgs =>
          restArgs.foldl
            (fun acc arg => s!"({acc})({exprToStringWithBound bound arg})")
            accPrefix
      let renderSelect (arr idx : String) : String :=
        s!"({arr}[{idx}])"
      let renderUpdate (arr idx val : String) : String :=
        s!"({arr}[{idx} := {val}])"
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
        | "Sequence.select" => renderSelect lhs rhs
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
        | "Map.Update" => renderUpdate lhs idx val
        | "Sequence.update" => renderUpdate lhs idx val
        | "update" => renderUpdate lhs idx val
        | "Map.Select" => renderAppliedResult (renderSelect lhs idx) [c]
        | "Sequence.select" => renderAppliedResult (renderSelect lhs idx) [c]
        | "select" => renderAppliedResult (renderSelect lhs idx) [c]
        | _ => callString op [lhs, idx, val]
      | .op _ id _, _ =>
        let op := ppCoreIdent id
        match fixedOpArity? op with
        | some arity =>
          if args.length <= arity then
            callString op (args.map (exprToStringWithBound bound))
          else
            let appliedPrefix := callString op ((args.take arity).map (exprToStringWithBound bound))
            renderAppliedResult appliedPrefix (args.drop arity)
        | none =>
          callString op (args.map (exprToStringWithBound bound))
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
  | .typeDecl t =>
    match t with
    | .con c => s!"type {c.name}{typeParamsToString c.numargs};"
    | .syn s => s!"type {s.name} := {tyToString (.forAll [] s.type)};"
    | .data ds => String.intercalate "\n" (ds.map datatypeDeclToString)
  | .axiom a => s!"axiom {CoreIdent.toPretty a.name}: {exprToString a.e};"
  | .var name ty e =>
    match e with
    | some rhs => s!"var {CoreIdent.toPretty name} : {tyToString ty} := {exprToString rhs};"
    | none => s!"var {CoreIdent.toPretty name} : {tyToString ty};"
  | .distinct lbl es =>
    let esStr := String.intercalate ", " (es.map exprToString)
    s!"distinct [{CoreIdent.toPretty lbl}] {esStr};"

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

end ToCore

end VerusLean
