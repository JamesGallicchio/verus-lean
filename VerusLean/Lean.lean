import VerusLean.VLIR
import VerusLean.VerusBuiltins

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
  | .Bool => return mkIdent ``_root_.Bool
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
    t1.foldrM (`($(·) → $(·))) t2
  | _ => throwError "unsupported type: {repr t}"

partial def Expr.toSyntax (e : Expr) : TermElabM Term := do
  match e with
  | .Var n => return n.toSyntax
  | .Unary op e =>
    let e ← e.toSyntax
    match op with
    | .Id => return e
    | .Not => `(! $e)
    | .BitNot => `(~~~ $e)
    | .Clip .Nat true => `($(mkIdent ``Int.natAbs) $e)
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
  | .If cond tt ff => do
    let cond ← cond.toSyntax
    let tt ← tt.toSyntax
    let ff ← ff.toSyntax
    `(if $cond then $tt else $ff)
  | _ =>
    throwError "unsupported expr: {repr e}"

def Defn.toSyntax (f : Defn) : CommandElabM (TSyntaxArray `command) :=
  match f with
  | { name
      typ_params
      params
      ret
      body
      decrease
      decrease_when
    } => do
  let ident := name.toSyntax
  let ty ← liftTermElabM ret.a.toSyntax
  let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    liftTermElabM (do
      let tyParams ← typ_params.mapM (fun (t: Ident) =>
        `(Lean.Parser.Term.bracketedBinderF| {$(t.toSyntax) : Type}))
      let params ← params.mapM (fun p => do
        let arg := p.name.toSyntax
        let type ← p.a.toSyntax
        `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
      return tyParams ++ params
    )
  let body : Term ← liftTermElabM <| do
    let body ← body.toSyntax
    match decrease_when with
    | some d => `(if $(← d.toSyntax) then $body else $(mkIdent ``undefined))
    | none => pure body
  let func ← liftTermElabM <| do
    if _h: decrease.size > 0 then
      let hd := Syntax.mkApp (mkIdent ``Int.natAbs) <| #[← (decrease[0]'_h).toSyntax ]
      let tl ← (decrease[1:].toArray).mapM (·.toSyntax)
      let lexOrd : Term ←
        if tl.size > 0 then
          `( ( $hd, $tl,* ) )
        else
          pure hd
      `(def $ident $args* : $ty := $body
        termination_by $lexOrd
        decreasing_by all_goals (simp_wf; aesop (rule_sets := [$(mkIdent `VerusLean):ident]))
      )
    else
      `(def $ident $args* : $ty := $body)
  return #[func]

def Theorem.toSyntax (f : Theorem) : CommandElabM (TSyntaxArray `command) :=
  match f with
  | { name
      typ_params
      params
      require
      ensure
    } => do
  let ident := name.toSyntax
  let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
    liftTermElabM (do
      let tyParams ← typ_params.mapM (fun (t: Ident) =>
        `(Lean.Parser.Term.bracketedBinderF| {$(t.toSyntax) : Type}))
      let params ← params.mapM (fun p => do
        let arg := p.name.toSyntax
        let type ← p.a.toSyntax
        `(Lean.Parser.Term.bracketedBinderF| ($arg : $type) ))
      return tyParams ++ params
    )
  let hyps : TSyntaxArray `term ← liftTermElabM <| require.mapM (·.toSyntax)
  let concs : TSyntaxArray `term ← liftTermElabM <| ensure.mapM (·.toSyntax)
  let conc : Term := Option.getD (dflt := mkIdent ``True) <|
    ← concs.foldrM (fun h acc =>
        match acc with
        | some acc => `($h ∧ $acc)
        | none => pure h
      ) none
  let typ : Term ← hyps.foldrM (fun h acc => `($h → $acc)) conc
  let c ← `(command|
    theorem $ident $(args):bracketedBinder*
      : $typ
      := by sorry
  )
  return #[c]

def Decl.toSyntax (d : Decl) :=
  match d with
  | .Defn d => d.toSyntax
  | .Theorem t => t.toSyntax
