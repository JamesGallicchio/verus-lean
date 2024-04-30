import Lean

namespace VerusLean

def unwrapSpan (j : Lean.Json) : Except String Lean.Json :=
  Except.mapError (fun _ => s!"Unwrapping span: {j}") do
  j.getObjVal? "x"

structure Id where
  krate : String
  segments : List String

def Id.fromJson? (j : Lean.Json) : Except String Id := do
  let krate ← j.getObjValAs? String "krate"
  let segments ← j.getObjValAs? (List String) "segments"
  return {krate, segments}

inductive Typ
| uint (width : Nat)
| int (width : Nat)
| tuple (typs : List Typ)
| datatype (id : Id) (typs : List Typ)

partial def Typ.fromJson? (j : Lean.Json) : Except String Typ :=
  match j.getObjVal? "Int" with
  | Except.ok i => do
    if (do i.getObjVal? "U").isOk then
      let width ← i.getObjValAs? Nat "U"
      return Typ.uint width
    if (do i.getObjVal? "I").isOk then
      let width ← i.getObjValAs? Nat "I"
      return Typ.int width
    throw s!"Type \"Int\" found but neither U nor I children:\n{i}"
  | Except.error _ =>
  match j.getObjVal? "Tuple" with
  | Except.ok tys => do
    return .tuple (← (← tys.getArr?).mapM Typ.fromJson?).toList
  | Except.error _ =>
  match j.getObjVal? "Datatype" with
  | Except.ok j => do
    let a1 ← j.getArrVal? 0
    let a2 ← j.getArrVal? 1
    let a3 ← j.getArrVal? 2
    let id ← Id.fromJson? a1
    let typs ← (← a2.getArr?).mapM Typ.fromJson?
    if a3 == .arr #[] then
      return .datatype id typs.toList
    else
      throw s!"third parameter of datatype is not nil: {j}"
  | Except.error _ =>
  throw s!"Type JSON not recognized: {j}"

instance : Lean.FromJson Typ where
  fromJson? := Typ.fromJson?

inductive Const
| int (val : Int)
| bool (b : Bool)

def Const.fromJson? (j : Lean.Json) : Except String Const :=
  Except.mapError ("Const: " ++ ·) do
    match j.getObjVal? "Int" with
    | Except.ok j => do
      let val ← j.getArrVal? 1
      let val : Array Int ← Lean.FromJson.fromJson? val
      return .int (val.foldr (· + (2^32) * ·) 0)
    | Except.error _ =>
    match j.getObjVal? "Bool" with
    | Except.ok j => do
      let b ← j.getBool?
      return .bool b
    | Except.error _ =>
    throw s!"Unrecognized Const: {j}"

inductive BinaryOp
| eq
| ne
| lt
| gt
| le
| ge
| and
| or

def BinaryOp.fromJson? (j : Lean.Json) : Except String BinaryOp :=
  Except.mapError ("BinOp: " ++ ·) do
  match j.getObjVal? "Eq" with
  | Except.ok j =>
    if j == .str "Spec" then
      return .eq
    else
      throw "Eq not Spec"
  | Except.error _ =>
  match j.getObjVal? "Inequality" with
  | Except.ok j =>
    match j.getStr? with
    | .ok "Lt" => return .lt
    | .ok "Le" => return .le
    | .ok "Gt" => return .gt
    | .ok "Ge" => return .ge
    | _ =>
      throw s!"Inequality value not recognized: {j}"
  | Except.error _ =>
  match j.getStr? with
  | .ok "And" => return .and
  | .ok "Or" => return .or
  | _ =>
  throw s!"Unrecognized binary op: {j}"

inductive Pattern
| var (name : String)

def Pattern.fromJson? (j : Lean.Json) : Except String Pattern :=
  Except.mapError ("Pattern: " ++ ·) do
  match j.getObjVal? "Var" with
  | Except.ok j => do
    let name ← j.getObjVal? "name"
    let name ← name.getArrVal? 0
    let name ← name.getStr?
    return .var name
  | Except.error _ =>
  throw s!"Unrecognized pattern: {j}"

mutual
inductive PureExpr
| var (name : String)
| const (c : Const)
| block (stms : List PureStmt) (expr : PureExpr)
| binary (op : BinaryOp) (lhs rhs : PureExpr)

inductive PureStmt where
| decl (pattern : Pattern) (init : PureExpr)
end

mutual
partial def PureExpr.fromJson? (j : Lean.Json) : Except String PureExpr :=
  Except.mapError ("Expr: " ++ ·) do
  match j.getObjVal? "Var" with
  | Except.ok j =>
    Except.mapError ("Var: " ++ ·) do
    let name ← j.getArrVal? 0
    let name ← name.getStr?
    return .var name
  | Except.error _ =>
  match j.getObjVal? "Const" with
  | Except.ok j =>
    return .const <| ← Const.fromJson? j
  | Except.error _ =>
  match j.getObjVal? "Block" with
  | Except.ok j =>
    Except.mapError ("Block: " ++ ·) do
    let a1 ← j.getArrVal? 0
    let a2 ← j.getArrVal? 1
    let stms ← (← a1.getArr?).mapM (do PureStmt.fromJson? <| ← unwrapSpan ·)
    let expr ← PureExpr.fromJson? (← unwrapSpan a2)
    return .block stms.toList expr
  | Except.error _ =>
  match j.getObjVal? "Binary" with
  | Except.ok j =>
    Except.mapError ("Binary: " ++ ·) do
    let a1 ← j.getArrVal? 0
    let op ← BinaryOp.fromJson? a1
    let a2 ← j.getArrVal? 1
    let lhs ← PureExpr.fromJson? (← unwrapSpan a2)
    let a3 ← j.getArrVal? 2
    let rhs ← PureExpr.fromJson? (← unwrapSpan a3)
    return .binary op lhs rhs
  | Except.error _ =>
  throw s!"Unrecognized Expr: {j}"

partial def PureStmt.fromJson? (j : Lean.Json) : Except String PureStmt :=
  Except.mapError ("Stmt: " ++ ·) do
  match j.getObjVal? "Decl" with
  | Except.ok j => do
    let pattern ← j.getObjVal? "pattern"
    let pattern ← Pattern.fromJson? (← unwrapSpan pattern)
    let init ← j.getObjVal? "init"
    let init ← PureExpr.fromJson? (← unwrapSpan init)
    return .decl pattern init
  | Except.error _ =>
  throw s!"Unrecognized Stmt: {j}"
end

structure Param where
  name : String
  typ : Typ

def Param.fromJson? (j : Lean.Json) : Except String Param :=
  Except.mapError ("Param: " ++ ·) do
  let name ← (← (← j.getObjVal? "name").getArrVal? 0).getStr?
  let typ ← j.getObjValAs? Typ "typ"
  return {
    name, typ
  }

structure Function where
  id : Id
  params : List Param
  ret : Param
  require : List PureExpr
  ensure : List PureExpr

partial def Function.fromJson? (j : Lean.Json) : Except String Function :=
  Except.mapError ("Function: " ++ ·) do
  let id ← (do
    let name ← j.getObjVal? "name"
    let path ← name.getObjVal? "path"
    let id ← Id.fromJson? path
    return id )
  let params ← (
    Except.mapError ("Params: " ++ ·) do
    let p ← j.getObjVal? "params"
    let arr ← p.getArr?
    let arr' ← arr.mapM (fun pj => do
      let unwrapped ← unwrapSpan pj
      Param.fromJson? unwrapped)
    return arr'.toList )
  let ret ← (
    Except.mapError ("Return: " ++ ·) do
    let ret ← j.getObjVal? "ret"
    let unwrapped ← unwrapSpan ret
    return ← Param.fromJson? unwrapped )
  let require ← (
    Except.mapError ("Require: " ++ ·) do
    let r ← j.getObjVal? "require"
    let arr ← r.getArr?
    let arr' ← arr.mapM (fun rj => do
      PureExpr.fromJson? (← unwrapSpan rj))
    return arr'.toList)
  let ensure ← (
    Except.mapError ("Ensure: " ++ ·) do
    let r ← j.getObjVal? "ensure"
    let arr ← r.getArr?
    let arr' ← arr.mapM (fun rj => do
      PureExpr.fromJson? (← unwrapSpan rj))
    return arr'.toList)
  dbgTrace s!"Function {id.segments} has requires {require.length}" <| fun () =>
  return {
    id,
    params,
    ret,
    require,
    ensure
  }
