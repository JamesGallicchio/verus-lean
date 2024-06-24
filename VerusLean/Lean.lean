import VerusLean.VLIR

namespace VerusLean

open Lean Elab Command

def datatypeMap : HashMap Path (Array Term → TermElabM Term) :=
  .ofList [
    ( ⟨some "core", #["result", "Result"]⟩
    , fun
      | #[A,B] => do
        let exc := mkIdent ``Except
        `($exc $A $B)
      | _ => throwError "Result arity should be 2?"
    )
  ]

def Ident.toSyntax (i : Ident) : Lean.Ident :=
  mkIdent (.mkSimple i)

partial def Path.toSyntax (i : Path) : Lean.Ident :=
  Lean.mkIdent <| i.segments.foldl
    (init := i.krate.elim .anonymous .mkStr1)
    (·.str ·)

partial def Typ.toSyntax (t : Typ) : TermElabM Term := do
  match t with
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
        return mkIdent `UInt32
      | _ =>
        throwError "Signed int type: Unsupported width {width}"
    | .USize => return mkIdent ``USize
    | .Int => return mkIdent ``Int
    | .Nat => return mkIdent ``Nat
  | .Datatype id params => do
    match datatypeMap.find? id with
    | none =>
      throwError "Couldn't find datatype in datatype map"
    | some handler =>
      handler (← params.mapM Typ.toSyntax)
  | _ => throwError "unsupported type: {repr t}"

def Expr.toSyntax (e : Expr) : TermElabM Term :=
  match e with
  | .Var n => return mkIdent (.mkStr1 n)
  | .Binary op lhs rhs => do
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
    | _ => throwError "unsupported binop {repr op}"
  | .Const (.Int i) =>
    return Syntax.mkNumLit (toString i)
  | .Const (.Bool b) =>
    return Syntax.mkCApp (.mkStr1 <| toString b) #[]
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
