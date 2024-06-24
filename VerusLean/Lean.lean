import VerusLean.VLIR

namespace VerusLean

open Lean Elab Command

def Ident.toSyntax (i : Ident) : Lean.Ident :=
  mkIdent (.mkSimple i)

partial def Path.toSyntax (i : Path) : Lean.Ident :=
  Lean.mkIdent <| i.segments.foldl
    (init := i.krate.elim .anonymous .mkStr1)
    (·.str ·)

def handleDatatype (id : Path) (params : Array Term) : TermElabM Term :=
  match id with
  | { krate := none, segments := #["tuple%0"] } =>
    match params.back? with
    | none => return mkIdent ``Unit
    | some last =>
      params.pop.foldrM (`(· × ·)) last
  | _ =>
  match datatypeMap.find? id with
  | some handler => handler params
  | none =>
    throwError "Cannot handle datatype {repr id} with parameters {params}"
where datatypeMap : HashMap Path (Array Term → TermElabM Term) :=
  .ofList [
    ( ⟨some "core", #["result", "Result"]⟩
    , fun
      | #[A,B] => do
        let exc := mkIdent ``Except
        `($exc $A $B)
      | _ => throwError "Result arity should be 2?"
    )
  ]

partial def Typ.toSyntax (t : Typ) : TermElabM Term := do
  match t with
  | .Bool => return mkIdent ``Bool
  | .Int ityp =>
    match ityp with
    | .I width =>
      match width with
      | _ =>
        throwError "Signed int type: Unsupported width {width}"
    | .ISize =>
      throwError "Signed int type: Unsupported width ISize"
    | .U width =>
      match width with
      | 32 =>
        return mkIdent ``UInt32
      | _ =>
        throwError "Signed int type: Unsupported width {width}"
    | .USize => return mkIdent ``USize
    | .Int => return mkIdent ``_root_.Int
    | .Nat => return mkIdent ``Nat
  | .Datatype id params => do
    handleDatatype id (← params.mapM Typ.toSyntax)
  | .Lambda t1 t2 =>
    let t1 ← t1.mapM (·.toSyntax)
    let t2 ← t2.toSyntax
    t1.foldrM (`(· → ·)) t2
  | _ => throwError "unsupported type: {repr t}"

partial def Expr.toSyntax (e : Expr) : TermElabM Term := do
  match e with
  | .Var n => return mkIdent (.mkStr1 n)
  | .Unary op e =>
    let e ← e.toSyntax
    match op with
    | .Id => return e
    | .Not => `(! $e)
    | .BitNot => `(~~~ $e)
    | .Clip .Nat true =>
      return mkIdent ``Int.natAbs
    | _ => throwError "unsupported binop {repr op}"
  | .Binary op lhs rhs =>
    let lhs ← lhs.toSyntax
    let rhs ← rhs.toSyntax
    match op with
    | .Eq =>
      `($lhs = $rhs)
    | .Ne =>
      `($lhs ≠ $rhs)
    | .Inequality .Lt =>
      `($lhs < $rhs)
    | .Inequality .Le =>
      `($lhs ≤ $rhs)
    | .Inequality .Gt =>
      `($lhs > $rhs)
    | .Inequality .Ge =>
      `($lhs ≥ $rhs)
    | .And =>
      `($lhs ∧ $rhs)
    | .Or =>
      `($lhs ∨ $rhs)
    | .Implies =>
      `($lhs → $rhs)
    | .Xor =>
      `($lhs ^^^ $rhs)
    | .Arith .Add =>
      `($lhs + $rhs)
    | .Arith .Mul =>
      `($lhs * $rhs)
    | .Arith .Sub =>
      `($lhs - $rhs)
    | .Arith .EuclideanDiv =>
      `($lhs / $rhs)
    | .Arith .EuclideanMod =>
      `($lhs % $rhs)
    | .Bitwise .Shl =>
      `($lhs <<< $rhs)
    | .Bitwise .Shr =>
      `($lhs >>> $rhs)
    | .Bitwise .BitOr =>
      `($lhs ||| $rhs)
    | .Bitwise .BitAnd =>
      `($lhs &&& $rhs)
    | .Bitwise .BitXor =>
      `($lhs ^^^ $rhs)
    | _ => throwError "unsupported binop {repr op}"
  | .Const c =>
    match c with
    | .Int i =>
      return Syntax.mkNumLit i
    | .Bool b=>
      return Syntax.mkCApp (.mkStr1 <| toString b) #[]
    | .StrSlice s =>
      return Syntax.mkStrLit s
  | .App f args =>
    let f ← f.toSyntax
    let args ← args.mapM (·.toSyntax)
    `($f $args*)
  | .StaticFun p =>
    return p.toSyntax
  | .Let decl e =>
    let init ← decl.a.toSyntax
    let e ← e.toSyntax
    `(let $(decl.name.toSyntax) := $init; $e)
  | .Quant q vs body =>
    match q with
    | .Forall =>
      let vs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
        vs.mapM (fun b => do `(bracketedBinder|
          ($(b.name.toSyntax) : $(← b.a.toSyntax))
        ))
      `(∀ $vs*, $(← body.toSyntax))
    | .Exists =>
      let vs : TSyntaxArray ``Lean.bracketedExplicitBinders ←
        vs.mapM (fun b => do `(Lean.bracketedExplicitBinders|
          ($(b.name.toSyntax):ident : $(← b.a.toSyntax))
        ))
      `(∃ $vs*, $(← body.toSyntax))
  | _ =>
    throwError "unsupported expr: {repr e}"

def Function.toSyntax (f : Function) : CommandElabM (TSyntaxArray `command) :=
  match f with
  | { name
      typ_params
      params
      ret
      require
      ensure
      decrease
      decrease_when
    } => do
  let ident := name.toSyntax
  let ty ← liftTermElabM ret.a.toSyntax
  let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    liftTermElabM <|
    params.mapM (fun p => do
      let arg := p.name.toSyntax
      let type ← p.a.toSyntax
      `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
  let hyps : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    liftTermElabM <|
    require.mapIdxM (fun i req => do
      let arg := mkIdent (.mkSimple s!"_h{i}")
      let type ← req.toSyntax
      `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
  let func ← `(opaque $ident $(args ++ hyps):bracketedBinder* : $ty)
  let ensures ←
    liftTermElabM <|
    ensure.mapIdxM (fun i ens => do
      let thmIdent := mkIdent <| ident.getId.str s!"_{i}"
      `(theorem $thmIdent $(args ++ hyps):bracketedBinder* :
          let $(ident) : $(←ret.a.toSyntax) :=
            $ident $(params.map (·.name.toSyntax)):term*
          $(← ens.toSyntax)
        := sorry
      )
    )
  return #[func] ++ ensures
