import VerusLean.Verus

namespace VerusLean

open Lean Elab Command

partial def Id.toSyntax (i : Id) : Ident :=
  Lean.mkIdent <| i.segments.foldl (· ++ .mkStr1 ·) (.mkStr1 i.krate)

partial def Typ.toSyntax (t : Typ) : TermElabM Term := do
  match t with
  | .int ityp =>
    match ityp with
    | .signed width =>
      return mkIdent ↑("Int" ++ toString width)
    | .unsigned width =>
      return mkIdent ↑("UInt" ++ toString width)
    | .inf =>
      return mkIdent "Int"
  | .datatype id params => do
    `($(id.toSyntax) $(← params.toArray.mapM Typ.toSyntax)*)
  | .tuple tys => do
    tys.foldrM (fun a b => do
      `($(← Typ.toSyntax a) × $b))
      (← `( Unit ))

def PureExpr.toSyntax (e : PureExpr) : TermElabM Term :=
  match e with
  | .var n => return mkIdent n
  | .binary op lhs rhs => do
    let lhs ← lhs.toSyntax
    let rhs ← rhs.toSyntax
    match op with
    | .eq =>
      `($lhs = $rhs)
    | .ne =>
      `($lhs ≠ $rhs)
    | .lt =>
      `($lhs < $rhs)
    | .le =>
      `($lhs ≤ $rhs)
    | .gt =>
      `($lhs > $rhs)
    | .ge =>
      `($lhs ≥ $rhs)
    | .and =>
      `($lhs ∧ $rhs)
    | .or =>
      `($lhs ∨ $rhs)
  | .const (.int i) =>
    return Syntax.mkNumLit (toString i)
  | .const (.bool b) =>
    return Syntax.mkCApp (toString b) #[]
  | .block _ _ =>
    throwError "blocks currently unsupported"

def Function.toSyntax (f : Function) : CommandElabM Syntax :=
  match f with
  | { id
      params
      ret
      require
      ensure
    } => do
  let ident := id.toSyntax
  let ty ← liftTermElabM ret.typ.toSyntax
  let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    params.toArray.mapM (fun p => do
      return mkNode _ (#[
        mkAtom "(", mkIdent p.name, mkAtom ":", ←liftTermElabM p.typ.toSyntax, mkAtom ")"
      ]))
  let hyps : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    require.toArray.mapIdxM (fun i req => do
      return mkNode _ (#[
        mkAtom "(",
        mkIdent s!"_h{i}",
        mkAtom ":",
        ←liftTermElabM <| req.toSyntax,
        mkAtom ")"
      ]))
  `(opaque $ident $(args ++ hyps):bracketedBinder* : $ty)
