import VerusLean.VLIR.Defs

/-!

  Pretty printing of the `VLIR`.

  These functions were originally used to output the Lean code directly.
  However, delaboration is now the current strategy (see `Delab.lean`).
  We keep these functions around for `ToString` purposes.

-/

namespace VerusLean

def Ident.pp (i : Ident) : String := i.toString

def TypDecoration.pp (dec : TypDecoration) : String :=
  match dec with
  | .Ref      => "&"
  | .MutRef   => "&mut "
  | .Box      => "Box "
  | .Rc       => "Rc "
  | .Arc      => "Arc "
  | .Ghost    => "Ghost "
  | .Tracked  => "Tracked "
  | .ConstPtr => "*const "

def Typ.pp (ty : Typ) : String :=
  match ty with
  | .Empty => "Empty"
  | .Unit => "Unit"
  | .Tuple t₁ t₂ => s!"({Typ.pp t₁}) × ({Typ.pp t₂})"
  | .Bool => "Bool"
  | .Int => "Int"
  | .Nat => "Nat"
  | .UInt w => s!"UInt{w}"
  | .SInt w => s!"Int{w}"
  | .Char => "Char"
  | .StrSlice => "String"
  | .Array ty => s!"Array ({ty.pp})"
  | .TypParam i => i
  | .SpecFn params ret =>
    if params.length > 0 then
      let params := params.map Typ.pp |> String.intercalate "→"
      s!"{params} → {ret.pp}"
    else
      s!"{ret.pp}"
  | .Decorated dec ty => s!"{dec.pp}{ty.pp}"
  | .Struct name params
  | .Enum name params =>
    if params.length > 0 then
      let params := params.attach.map
        (fun ⟨ty, _⟩ => if ty.height = 1 then Typ.pp ty else s!"({Typ.pp ty})")
      let params := String.intercalate " " params
      s!"{name} {params}"
    else
      name
  | .AirNamed name => s!"Air({name})"

def Const.pp (c : Const) : String :=
  match c with
  | .Bool b => toString b
  | .Int i => toString i
  | .StrSlice s => s
  | .Char c => toString c

def IntRange.pp (r : IntRange) : String :=
  match r with
  | .Int => "Int"
  | .Nat => "Nat"
  | .U u => s!"U({u})"
  | .I i => s!"I({i})"
  | .USize => "USize"
  | .ISize => "ISize"
  | .Char => "Char"

def BitwiseOp.pp (op : BitwiseOp) : String :=
  match op with
  | .BitXor => " ^^^ "
  | .BitAnd => " &&& "
  | .BitOr  => " ||| "
  | .Shr _ => " >>> "
  | .Shl _ _ => " <<< "

def ArithOp.pp (op : ArithOp) : String :=
  match op with
  | .Add => " + "
  | .Sub => " - "
  | .Mul => " * "
  | .EuclideanDiv => " / "
  | .EuclideanMod => " % "

def InequalityOp.pp (op : InequalityOp) : String :=
  match op with
  | .Lt => " < "
  | .Le => " ≤ "
  | .Gt => " > "
  | .Ge => " ≥ "

def UnaryOp.pp (op : UnaryOp) : String :=
  match op with
  | .Not => "!"
  | .BitNot _ => "!"
  | .Old => "old "
  | .Proj dt variant field _ _ => s!"{dt}.{field} of {variant}"
  | .IsVariant dt variant => s!"is {dt}.{variant}: "
  | .Box t => t.pp
  | .Unbox t => t.pp
  | _ => "unsupported unary op"

def BinaryOp.pp (op : BinaryOp) : String :=
  match op with
  | .And => " ∧ "
  | .Or => " ∨ "
  | .Xor => " ^^ "
  | .Implies => " → "
  | .Eq _ => " = "
  | .Ne => " ≠ "
  | .Inequality ineq => InequalityOp.pp ineq
  | .Arith arith _ => ArithOp.pp arith
  | .Bitwise bitwise _ => BitwiseOp.pp bitwise

def Quant.pp (q : Quant) : String :=
  match q with
  | .Forall => "∀"
  | .Exists => "∃"

mutual

partial def Bind.pp (b : Bind) : String :=
  match b with
  | .Let v ty e =>
    let tyStr := Typ.pp ty
    let expStr := Exp.pp e
    s!"let {v} : {tyStr} := {expStr}; "
  | .Quant q vars _trigs =>
    let qStr := Quant.pp q
    let varsStr := vars.map (fun ⟨i, ty⟩ => s!"({i} : {ty.pp})")
    s!"{qStr} {varsStr}, "
  | .Lambda vars =>
    let varsStr := vars.map (fun ⟨i, ty⟩ => s!"({i} : {ty.pp})")
    s!"λ {varsStr} =>"

partial def Exp.pp (e : Exp) : String :=
  match e with
  | .Const c => Const.pp c
  | .Var ident => ident
  | .Call fn _ exps =>
    let fn := CallFun.name fn
    let exps := exps.map Exp.pp
    let exps := String.intercalate ", " exps
    fn ++ "(" ++ exps ++ ")"
  | .CallLambda body exps =>
    let body := Exp.pp body
    let exps := exps.map Exp.pp
    let exps := String.intercalate ", " exps
    body ++ "(" ++ exps ++ ")"
  | .StructCtor dt fields =>
    let fs := fields.map (fun ⟨i, e⟩ => s!"{i}: {Exp.pp e}")
    let fs := String.intercalate ", " fs
    "({ " ++ fs ++ "} : " ++ dt ++ ")"
  | .EnumCtor dt variant data =>
    s!"{dt}.{variant} {data.map (fun ⟨i, e⟩ => s!"({i}: {Exp.pp e})")}"
  | .TupleCtor _ data =>
    s!"{data.map (fun e => s!"{Exp.pp e}")}" -- TODO
  | .Unary op e =>
    let e := Exp.pp e
    "(" ++ UnaryOp.pp op ++ e ++ ")"
  | .Binary op lhs rhs =>
    let lhs := Exp.pp lhs
    let rhs := Exp.pp rhs
    "(" ++ lhs ++ BinaryOp.pp op ++ rhs ++ ")"
  | .If cond b₁ b₂ =>
    let cond := Exp.pp cond
    let b₁ := Exp.pp b₁
    let b₂ := Exp.pp b₂
    "if (" ++ cond ++ ") then (" ++ b₁ ++ ") else (" ++ b₂ ++ ")"
  | .Bind bnd exp =>
    let bnd := Bind.pp bnd
    let exp := Exp.pp exp
    bnd ++ exp
  | .ArrayLiteral es =>
    let es := es.map Exp.pp
    let es := String.intercalate ", " es
    s!"[{es}]"
  | .MatchBlock (scrutinee, _) body =>
    let scrutinee := Exp.pp scrutinee
    let body := Exp.pp body
    s!"match {scrutinee} BEGIN {body} END"


end /- mutual -/

partial def LValue.pp : LValue → String
  | .Var n => n
  | .Proj base dt variant field _ _ =>
    s!"{LValue.pp base}.{dt}.{variant}.{field}"
  | .Proj' base size field =>
    s!"{LValue.pp base}.tuple{size}.{field}"

def AssertQueryMode.pp : AssertQueryMode → String
  | .NonLinear => "NonLinear"
  | .BitVector => "BitVector"
  | .Other n => n

partial def Stm.pp (stm : Stm) : String :=
  match stm with
  | .Call fn _ args =>
    let args := args.map Exp.pp
    s!"{fn} {args}"
  | .Assert e => s!"assert {Exp.pp e}"
  | .AssertBitVector reqs ens =>
    s!"assertBitVector {reqs.map Exp.pp} {ens.map Exp.pp}"
  | .AssertQuery mode stm => s!"assertQuery[{AssertQueryMode.pp mode}] {Stm.pp stm}"
  | .AssertLean e => s!"assertLean {Exp.pp e}"
  | .Assume e => s!"assume {Exp.pp e}"
  | .Assign lhs ty rhs _ =>
    let tyStr := Typ.pp ty
    let rhs := Exp.pp rhs
    s!"let {LValue.pp lhs} : {tyStr} := {rhs}"
  | .DeadEnd stm => s!"deadEnd {Stm.pp stm}"
  | .Return e =>
    match e with
    | none => ""
    | some e => s!"return {Exp.pp e}"
  | .If cond b₁ b₂ =>
    let cond := Exp.pp cond
    let b₁ := Stm.pp b₁
    match b₂ with
    | none    => s!"if ({cond}) then ({b₁})"
    | some b₂ => s!"if ({cond}) then ({b₁}) else ({Stm.pp b₂})"
  | .OpenInvariant stm => s!"openInvariant {Stm.pp stm}"
  | .Block stms =>
    let stms := stms.map Stm.pp
    let stms := String.intercalate "\n" stms
    s!"{stms}\n"
  | _ => "stm feature not yet implemented"


instance Typ.toString : ToString Typ := ⟨Typ.pp⟩
instance Const.toString : ToString Const := ⟨Const.pp⟩
instance BitwiseOp.toString : ToString BitwiseOp := ⟨BitwiseOp.pp⟩
instance ArithOp.toString : ToString ArithOp := ⟨ArithOp.pp⟩
instance InequalityOp.toString : ToString InequalityOp := ⟨InequalityOp.pp⟩
instance UnaryOp.toString : ToString UnaryOp := ⟨UnaryOp.pp⟩
instance BinaryOp.toString : ToString BinaryOp := ⟨BinaryOp.pp⟩
instance Quant.toString : ToString Quant := ⟨Quant.pp⟩
instance Bind.toString : ToString Bind := ⟨Bind.pp⟩
instance Exp.toString : ToString Exp := ⟨Exp.pp⟩
instance LValue.toString : ToString LValue := ⟨LValue.pp⟩
instance Stm.toString : ToString Stm := ⟨Stm.pp⟩

def Assertion.pp (a : Assertion) : String :=
  let ⟨name, decls, body⟩ := a
  s!"{name} {decls.map Prod.fst} := {body}"

def SpecFn.pp (f : SpecFn) : String :=
  let ⟨name, args, ret, _, body, _, _⟩ := f -- todo: decreases clause
  if args.length > 0 then
    s!"def {name} {args} : {ret} := {body}"
  else
    s!"def {name} : {ret} := {body}"

def ProofFn.pp (f : ProofFn) : String :=
  let ⟨name, args, _requires, ensures, _body, _locals⟩ := f
  if args.length > 0 then
    s!"theorem {name} {args} : {ensures} := by sorry"
  else
    s!"theorem {name} : {ensures} := by sorry"

def ExecFn.pp (f : ExecFn) : String :=
  let ⟨name, args, _retName, ret, _requires, _ensures, _body, _locals⟩ := f
  if args.length > 0 then
    s!"def {name} {args} : {ret} := by sorry"
  else
    s!"def {name} : {ret} := by sorry"

def Struct.pp (s : Struct) : String :=
  let ⟨name, _, fields⟩ := s
  let fields := fields.map (fun ⟨name, ty⟩ => s!"{name} : {ty}")
  s!"structure {name} ({fields})"

def EnumField.pp (f : EnumField) : String :=
  match f with
  | .labeled name data  => s!"| {name} {data} "
  | .tuple name ts      => s!"| {name} : {ts}"

def Enum.pp (e : Enum) : String :=
  let ⟨name, _, fields⟩ := e
  s!"inductive {name} where {fields.map EnumField.pp}"

def FuncCheckSst.pp (f : FuncCheckSst) : String :=
  let ⟨name, reqs, enss, decls⟩ := f
  s!"theorem {name} ({decls.map Prod.fst} : {decls.map Prod.snd}) : {reqs} → {enss}"

def Decl.pp (d : Decl) : String :=
  match d with
  | .assertion a => Assertion.pp a
  | .specFn f => SpecFn.pp f
  | .proofFn f => ProofFn.pp f
  | .execFn f => ExecFn.pp f
  | .struct s => Struct.pp s
  | .enum e => Enum.pp e
  | .func f => FuncCheckSst.pp f
  | .mutualBlock ds => s!"mutual\n{ds.map Decl.pp}\nend"

instance Assertion.toString : ToString Assertion := ⟨Assertion.pp⟩
instance SpecFn.toString : ToString SpecFn := ⟨SpecFn.pp⟩
instance ProofFn.toString : ToString ProofFn := ⟨ProofFn.pp⟩
instance ExecFn.toString : ToString ExecFn := ⟨ExecFn.pp⟩
instance Struct.toString : ToString Struct := ⟨Struct.pp⟩
instance Decl.toString : ToString Decl := ⟨Decl.pp⟩

end VerusLean
