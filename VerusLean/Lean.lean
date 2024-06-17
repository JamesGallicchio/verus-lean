import VerusLean.VLIR

namespace VerusLean

open Lean Elab Command

def datatypeMap : HashMap Id (List Term → TermElabM Term) :=
  .ofList [
    ( ⟨"core", ["result", "Result"]⟩
    , fun
      | [A,B] => do
        let exc := mkIdent ``Except
        `($exc $A $B)
      | _ => throwError "Result arity should be 2?"
    )
  ]

partial def Id.toSyntax (i : Id) : Ident :=
  Lean.mkIdent <| i.segments.foldl (· ++ .mkStr1 ·) (.mkStr1 i.krate)

partial def Typ.toSyntax (t : Typ) : TermElabM Term := do
  match t with
  | .int ityp =>
    match ityp with
    | .signed width =>
      match width with
      | _ =>
        throwError "Signed int type: Unsupported width {width}"
    | .unsigned width =>
      match width with
      | 32 =>
        return mkIdent `UInt32
      | _ =>
        throwError "Signed int type: Unsupported width {width}"
    | .inf =>
      return mkIdent `Int
  | .datatype id params => do
    match datatypeMap.find? id with
    | none =>
      throwError "Couldn't find datatype in datatype map"
    | some handler =>
      handler (← params.mapM Typ.toSyntax)
  | .tuple tys => do
    tys.foldrM (fun a b => do
      `($(← Typ.toSyntax a) × $b))
      (mkIdent ``Unit)

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

def Function.toSyntax (f : Function) : CommandElabM (TSyntaxArray `command) :=
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
    liftTermElabM <|
    params.toArray.mapM (fun p => do
      let arg := mkIdent p.name
      let type ← p.typ.toSyntax
      `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
  let hyps : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    liftTermElabM <|
    require.toArray.mapIdxM (fun i req => do
      let arg := mkIdent s!"_h{i}"
      let type ← req.toSyntax
      `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
  let func ← `(opaque $ident $(args ++ hyps):bracketedBinder* : $ty)
  let ensures ←
    liftTermElabM <|
    ensure.toArray.mapIdxM (fun i ens => do
      let thmIdent := mkIdent <| ident.getId.str s!"_{i}"
      `(theorem $thmIdent $(args ++ hyps):bracketedBinder* :
          let $(mkIdent f.ret.name) : $(←f.ret.typ.toSyntax) :=
            $ident $(params.toArray.map (mkIdent ·.name)):term*
          $(← ens.toSyntax)
        := sorry
      )
    )
  return #[func] ++ ensures
