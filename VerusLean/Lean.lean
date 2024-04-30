import VerusLean.Verus

namespace VerusLean

open Lean Elab Command

partial def Id.toSyntax (i : Id) : Ident :=
  Lean.mkIdent <| i.segments.foldl (· ++ .mkStr1 ·) (.mkStr1 i.krate)

partial def Typ.toSyntax (t : Typ) : TermElabM Term := do
  match t with
  | .int width =>
    return mkIdent ↑("Int" ++ toString width)
  | .uint width =>
    return mkIdent ↑("UInt" ++ toString width)
  | .datatype id params => do
    `($(id.toSyntax) $(← params.toArray.mapM Typ.toSyntax)*)
  | .tuple tys => do
    tys.foldrM (fun a b => do
      `($(← Typ.toSyntax a) × $b))
      (← `( Unit ))

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
  `(opaque $ident : $ty)
