import VerusLean.VLIR.Defs
import VerusLean.VLIR.Pp
import VerusLean.Tactic.ByVerus
import Lean.Elab
import VerusLean.Vstd.Seq.Defs
import VerusLean.Vstd.Set.Defs
import VerusLean.Vstd.Map.Defs
import VerusLean.VLIR.Translation

open Lean in
def String.toIdent (s : String) : CoreM Lean.Ident :=
  return mkIdent <| .mkSimple s

open Lean in
def String.toBinderIdent (s : String) : CoreM (TSyntax `Lean.binderIdent) := do
  let i ← String.toIdent s
  `(Lean.binderIdent| $i:ident)

namespace VerusLean

/-
  TODOs:

  - Develop a method of parenthesizing expressions/terms as they are built
    (especially the binary ones) that takes into account the underlying
    precedences of the sub-expressions. For example, (a + b) * (c + d)
    currently gets elaborated as a + (b * c) + d, since multiplication
    has higher precedence than addition.
    - One solution is to return a pair of `(Term × Precedence)`, or to operate
      in a wrapper monad for `CoreM` that has a precendence.
-/

open Lean Syntax Elab Command Parser Term Parser.Command Parser.Term

private def trueIdent : Lean.Ident := mkIdent ``true
private def falseIdent : Lean.Ident := mkIdent ``false
private def TrueIdent : Lean.Ident := mkIdent ``True
private def FalseIdent : Lean.Ident := mkIdent ``False
private def ArrayIdent : Lean.Ident := mkIdent ``Array


inductive Air where
  | named (name : String)

def Ident.toIdent (i : Ident) : CoreM Lean.Ident := do
  -- Drop the head of the pathed identifier if it matches the current namespace
  let ⟨h, tl⟩ := i.uncons
  let ns ← getCurrNamespace
  if h = ns then
    return mkIdent tl
  else
    return mkIdent i

def Ident.toIdent' (i : Ident) : Lean.Ident :=
  mkIdent i

def Typ.toTerm (ty : Typ) : CoreM Term := do
  match ty with
  | .Empty => return mkIdent ``_root_.Empty
  | .Unit => return mkIdent ``_root_.Unit
  | .Tuple ty₁ ty₂ => do
    let ty₁ ← ty₁.toTerm
    let ty₂ ← ty₂.toTerm
    -- CC: TODO Dependent typing?
    `($ty₁ × $ty₂)
  | .Bool => return mkIdent ``_root_.Bool
  | .Int => return mkIdent ``_root_.Int
  | .Nat => return mkIdent ``_root_.Nat
  | .UInt _ => return mkIdent ``_root_.UInt32
  | .SInt _ => `(BitVec 32)
  | .Char => return mkIdent ``_root_.Char
  | .StrSlice => return mkIdent ``_root_.String
  | .Array t => do
    let t ← t.toTerm
    `($ArrayIdent $t)
  | .TypParam name =>
    let nameAsIdent ← name.toIdent
    return nameAsIdent
  | .SpecFn params ret =>
    let r ← ret.toTerm
    let params := params.attach
    params.foldlM (init := r) (fun s ⟨ty, _⟩ => do
      let tyTerm ← ty.toTerm
      `($s:term → $tyTerm:term))
  | .Decorated _ ty =>
    -- TODO: Ignore the decoration for now
    ty.toTerm
  | .Struct name params
  | .Enum name params =>
    let nameAsIdent ← name.toIdent
    let params := params.attach
    params.foldlM (init := nameAsIdent) (fun s ⟨ty, _⟩ => do
      let tyTerm ← ty.toTerm
      `($s:term $tyTerm:term))
  | .AirNamed _ => return mkIdent ``Air


/--
  Makes a single explicit binder from an array of identifiers and a type.

  For example, if `as := #[a, b]` and `ty : Int`,
  then the result is `(a b : Int)`.
-/
private def makeBracketedBinder (as : Array String) (ty : Typ) : CoreM (TSyntax ``bracketedBinder) := do
  let ty ← ty.toTerm
  let binders : TSyntaxArray `ident ← as.mapM String.toIdent
  `(bracketedBinder| ($binders:ident* : $ty:term))

private def makeBracketedExplicitBinder (as : Array String) (ty : Typ) : CoreM (TSyntax ``bracketedExplicitBinders) := do
  let ty ← ty.toTerm
  let binders : TSyntaxArray `Lean.binderIdent ← as.mapM String.toBinderIdent
  `(bracketedExplicitBinders| ($binders:binderIdent* : $ty:term))

-- Polymorphic function to gather like-typed binder names
private def makeBinders (as : Array (String × Typ)) (binderFn : Array String → Typ → CoreM (TSyntax α)) : CoreM (TSyntaxArray α) := do
  let ⟨arr, likeTyps, ty?⟩ ← as.foldlM (init := (#[], #[], none)) (fun ⟨arr, likeTypIdents, ty?⟩ ⟨i, ty⟩ => do
    match ty? with
    | none =>
      return (arr, likeTypIdents.push i, some ty)
    | some ty' =>
      if ty = ty' then
        -- Defer mapping them into bracketed binder until diff detected
        return (arr, likeTypIdents.push i, some ty)
      else
        let binder ← binderFn likeTypIdents ty'
        return (arr.push binder, #[i], some ty))

  match ty? with
  | some ty => return arr.push (← binderFn likeTyps ty)
  | none =>
    if as.size = 0 then return #[]
    else throwError "empty array"

/--
  Makes a `TSyntaxArray ``bracketedBinder` with like types collected under
  a single bracketed binder.

  For example, if `as := #[a, b, c]` with `a b : Int` and `c : Nat`,
  then the result is `(a b : Int) (c : Nat)`.
-/
private def makeBracketedBinders (as : Array (String × Typ)) : CoreM (TSyntaxArray ``bracketedBinder) :=
  makeBinders as makeBracketedBinder

/--
  Makes a `TSyntaxArray ``explicitBinder` with like types collected under
  a single bracketed binder.

  For example, if `as := #[a, b, c]` with `a b : Int` and `c : Nat`,
  then the result is `(a b : Int) (c : Nat)`.
-/
private def makeBracketedExplicitBinders (as : Array (String × Typ)) : CoreM (TSyntaxArray ``bracketedExplicitBinders) :=
  makeBinders as makeBracketedExplicitBinder


def Const.toTerm (c : Const) : CoreM Term := do
  match c with
  | Const.Bool b =>
    -- See Lean.Init.Meta, for Quote Bool and mkCIdent
    -- No way to take the boolean directly?
    match b with
    | true => return trueIdent
    | false => return falseIdent
  | Const.Int i => return Syntax.mkNumLit s!"{i}"
  | Const.StrSlice _ => return mkIdent ``StrSlice
  | Const.Char _ => return mkIdent ``Char

-- CC: TODO figure out how to return just the op?
def BitwiseOp.toTerm (b : BitwiseOp) (lhs rhs : Term) : CoreM Term := do
  match b with
  | .BitXor  => `($lhs ^^^ $rhs)
  | .BitAnd  => `($lhs &&& $rhs)
  | .BitOr   => `($lhs ||| $rhs)
  | .Shr _   => `($lhs >>> $rhs)
  | .Shl _ _ => `($lhs <<< $rhs)

def ArithOp.toTerm (a : ArithOp) (lhs rhs : Term) : CoreM Term := do
  match a with
  | .Add => `($lhs + $rhs)
  | .Sub => `($lhs - $rhs)
  | .Mul => `($lhs * $rhs) -- CZ: temp fix for operator precedence, when to add parentheses?
  | .EuclideanDiv => `($lhs / $rhs)
  | .EuclideanMod => `($lhs % $rhs)

def InequalityOp.toTerm (i : InequalityOp) (lhs rhs : Term) : CoreM Term := do
  match i with
  | .Lt => `($lhs < $rhs)
  | .Le => `($lhs ≤ $rhs)
  | .Gt => `($lhs > $rhs)
  | .Ge => `($lhs ≥ $rhs)

def UnaryOp.toTerm (u : UnaryOp) (e : Term) : CoreM Term := do
  match u with
  | .Not => `(¬ ($e))
  | .BitNot _ => `(~~~ $e)
  | .Clip range _ =>
    -- TODO: Actual range-checking hypotheses
    -- For now, handle the most simple cases
    match range with
    | .Nat =>
      let natIdent := mkIdent `Nat
      let t ← `(($e : $natIdent))
      -- dbg_trace (← Lean.PrettyPrinter.formatTerm t)
      return t
    | .Int => let intIdent := mkIdent `Int; `(($e : $intIdent))
    | .USize => let uSizeIdent := mkIdent `USize; `(($e : $uSizeIdent))
    | .ISize => let iSizeIdent := mkIdent `ISize; `(($e : $iSizeIdent))
    | .Char => let charIdent := mkIdent `Char; `(($e : $charIdent))
    | _ => `($e)
  | .Trigger => `($e) -- Ignore trigger information when constructing terms
  | .Proj dt variant field _ _ =>
    dbg_trace s!"[Elab.lean]: UnaryOp.Proj: {dt} {variant} {field}"
    -- UnaryOp.Proj: Matching.life Arthropod legs
    let _dt ← dt.toIdent
    let _variant ← variant.toIdent
    let field ← field.toIdent
    let _defaultIdent := mkIdent `opaque_default
    `($e.$field)
    -- TODO: use dot notation if it is a structure,
    -- use match expression if it is an enum variable
    -- if isEnumVar then
    --   `(match $e:term with
    --   | $dt.$variant $field:ident .. => $field:ident
    --   | _ => $defaultIdent)
    -- else
    --   `($e.$field)
  | .Proj' size field =>
    if field ≥ size then
      throwError "Projection field {field} is out of bounds for a tuple of size {size}"
    if size = 2 && field = 1 then `($e.2) -- In p := (x,y), y is p.2 instead of p.2.1
    else
      let rec buildProdProj (e : Term) (n : Nat) : CoreM Term := do
        if n = 0 then `($e.1)
        else buildProdProj (←`($e.2)) (n - 1)
      buildProdProj e field
  | .IsVariant dt variant =>
    let dt ← dt.toIdent
    let variant ← variant.toIdent
    `(match $e:term with
      | $dt.$variant .. => $trueIdent
      | _ => $falseIdent)
  | .Box _ => `($e)   -- Ignore boxed-type information when constructing terms
  | .Unbox _ => `($e) -- Ignore boxed-type information when constructing terms
  | .HasType _ => `($e) -- todo

def BinaryOp.toTerm (b : BinaryOp) (lhs rhs : Term) : CoreM Term := do
  match b with
  | .And => `($lhs ∧ $rhs)
  | .Or => `($lhs ∨ $rhs)
  | .Xor => `($lhs ^^ $rhs)
  | .Implies => `($lhs → $rhs)
  | .Eq _ => `(($lhs) = ($rhs))
  | .Ne => `($lhs ≠ $rhs)
  | .Inequality ineq => ineq.toTerm lhs rhs
  | .Arith arith _ => arith.toTerm lhs rhs
  | .Bitwise bitwise _ => bitwise.toTerm lhs rhs

def CallFun.toIdent : CallFun → CoreM (Lean.Ident)
  | CallFun.Fun i => i.toIdent

private def VstdStr := "Vstd"

-- def getVstdSyntax (fn : Name) : CoreM Term := do
--   sorry

private def SeqVstdTranslationNames : Std.HashMap Lean.Name Lean.Name := Std.HashMap.ofList <|
  List.map (f := fun ⟨x, y⟩ => (String.toName s!"Vstd.Set_lib.{x}", String.toName y)) <| [
  ("is_full", "VSetInfF.isFull"),
  ]


def skipLetBindings (e : Exp) : Exp :=
  match e with
  | .Bind (.Let _ _ _) inner => skipLetBindings inner
  | _ => e

mutual

/--
  Constructs a Lean meta-`Term` associated with a `Bind`.

  In Verus, `Bind`s only store the names and types of the fresh variables
  (and the binding expression for `let`s). However, Lean expects binding
  terms to have their body expressions as well. Thus, this function
  expects the term `t` asosciated with the body expression after the bind.
  For example, `∀ (x : Int), x ≠ x + 1` would have a `Bind`
  representing `∀ (x : Int)`, and `t` would represent `x ≠ x + 1`.

  Because `Let` has an `Exp`, `Bind.toTerm` is mutually recursive
  with `Exp.toTerm`.
-/
partial def Bind.toTerm (b : Bind) (t : Term) : CoreM Term := do
  match b with
  | .Let v ty e =>
    let v ← v.toIdent
    let ty ← ty.toTerm
    let e ← e.toTerm
    -- See `letMVar` in `Lean.Parser.Term.lean`
    `(let $v : $ty := $e; $t)
  | .Quant q vars =>
    match q with
    | .Forall =>
      let vars ← makeBracketedBinders vars.toArray
      `(∀ $(vars):bracketedBinder*, $t)
    | .Exists => do
      if [] == vars then
        throwError "empty exists"
      let vars ← makeBracketedExplicitBinders vars.toArray
      `(∃ $(vars):bracketedExplicitBinders*, $t)
  | .Lambda vars =>
    -- TODO: Polymorphic binder this as well
    let varsLambda : TSyntaxArray ``funBinder ←
      vars.toArray.mapM (fun ⟨i, ty⟩ => do
        let i ← i.toIdent
        let ty ← ty.toTerm
        `(funBinder| ($i : $ty)))
    `(fun $(varsLambda):funBinder* => $t)

-- TODO: only include parentheses if the term is nontrivial
partial def VstdFnToTerm (fn : Ident) (exps : List Exp) : CoreM Term := do
  -- dbg_trace s!"[Elab.lean]: VstdFnToTerm: {fn} with {exps}"
  let (fnName, mapSyntax) := VstdSyntaxTable.get! fn
  let expsTerms : List Term ← exps.mapM (fun e => e.toTerm)
  mapSyntax (← Ident.toIdent fnName) expsTerms

partial def collectFieldsFromBind (exp : Exp) : CoreM (Array Lean.Ident) := do
  let rec walk (current : Exp) (fields : Array Lean.Ident) : CoreM (Array Lean.Ident) := do
    match current with
    | .Bind (.Let v _ _) inner => walk inner (fields.push (← v.toIdent))
    | _ => return fields
  walk exp #[]

-- Collect match arms from a chain of If expressions with IsVariant conditions
partial def collectMatchArmsFromIfChain (exp : Exp) : CoreM (Array (Term × Term)) := do
  -- dbg_trace s!"[Elab.lean]: collectMatchArmsFromIfChain: {exp}"

  let rec walkIfChain (current : Exp) (arms : Array (Term × Term)) : CoreM (Array (Term × Term)) := do
    match current with
    | .If (.Unary (UnaryOp.IsVariant dt variant) _scrutinee) thenBranch elseBranch =>
      -- dbg_trace s!"[Elab.lean]: Found IsVariant: {dt} {variant} in {scrutinee}"
      let dtIdent ← dt.toIdent
      let variantIdent ← variant.toIdent
      let fields ← match thenBranch with
        | .MatchBlock _ body => collectFieldsFromBind body
        | _ => throwError "Expected MatchBlock in thenBranch"

      let pattern ←
        if fields.isEmpty then `($dtIdent.$variantIdent ..)
                          else `($dtIdent.$variantIdent $fields:ident*)

      -- dbg_trace s!"[Elab.lean]: Match pattern: {pattern}"
      -- dbg_trace (← Lean.PrettyPrinter.formatTerm pattern)

      let body ← match thenBranch with
        | .MatchBlock _ body => (skipLetBindings body).toTerm
        | _ => throwError "Expected MatchBlock in thenBranch"
      -- dbg_trace s!"[Elab.lean]: Match body: {body}"
      -- dbg_trace (← Lean.PrettyPrinter.formatTerm body)

      let newArms := arms.push (pattern, body)
      walkIfChain elseBranch newArms

    | .If _ _ _ =>
      -- fallback case for other If expressions
      dbg_trace s!"[Elab.lean]: If case other than IsVariant not yet handled, likely because of the `is` operator, got: {current}"
      throwError s!"[Elab.lean]: If case other than IsVariant not yet handled, likely because of the `is` operator, got: {current}"

    | _ => -- Final case (should be a MatchBlock for the last variant)
      -- dbg_trace s!"[Elab.lean]: Final case in If chain, should be a MatchBlock: {current}"
      let dtIdent ← match current with
        | .MatchBlock (_, typ) _ => Ident.toIdent typ.pp.toName
        | _ =>
          dbg_trace s!"[Elab.lean]: Current is not a MatchBlock: {current}"
          throwError "Expected MatchBlock in final case"
      -- dbg_trace s!"[Elab.lean]: dtIdent: {dtIdent}"

      let variantIdent : Option Lean.Ident := match current with
        | .MatchBlock _ body => match body with
          | .Bind (.Let _ _ (.Unary (.Proj _ variant _ _ _) _)) _ =>
            -- Convert string to Name then to Ident
            some (mkIdent (Name.mkSimple variant))
          | _ => none
            -- dbg_trace s!"1 Expected MatchBlock in final case, got body: {body}"
        | _ =>
          dbg_trace "2 Expected MatchBlock in final case"
          none
      -- dbg_trace s!"[Elab.lean]: variantIdent: {variantIdent}"

      let pattern : CoreM Term := do
        if variantIdent.isNone then
          String.toIdent "_"
        else
          -- dbg_trace s!"[Elab.lean]: Match pattern with variant"
          let variantIdent := variantIdent.get!
          let fields ← match current with
            | .MatchBlock _ body => collectFieldsFromBind body
            | _ =>
              dbg_trace "3 Expected MatchBlock in thenBranch"
              throwError "Expected MatchBlock in thenBranch"
          -- dbg_trace s!"[Elab.lean]: Match fields: {fields}"
          if fields.isEmpty then `($dtIdent.$variantIdent ..)
                            else `($dtIdent.$variantIdent $fields:ident*)
      let pattern ← pattern -- CZ: not sure how to combine this with the above line
      -- dbg_trace s!"[Elab.lean]: Match pattern: {pattern}"
      -- dbg_trace (← Lean.PrettyPrinter.formatTerm pattern)

      let body ← match current with
        | .MatchBlock _ body => (skipLetBindings body).toTerm
        | _ => throwError "Expected MatchBlock in thenBranch"
      -- dbg_trace s!"[Elab.lean]: Match body: {body}"
      -- dbg_trace (← Lean.PrettyPrinter.formatTerm body)

      return arms.push (pattern, body)

  walkIfChain exp #[]


partial def Exp.toTerm (e : Exp) : CoreM Term := do
  match e with
  | .Const c => c.toTerm
  | .Var i => i.toIdent
  | .Call fn _ exps =>
    let fnName := match fn with | CallFun.Fun i => i
    if fnName.head = "Vstd" then
      VstdFnToTerm fnName exps
    else
      let fnIdent ← fn.toIdent
      let fn : Term ← `(term| $fnIdent)
      let args : List Term ← exps.filterMapM (fun e => do
        match e with
        | .Var "fuel%" => return none -- Skip the fuel variable
        | _ =>
          let t ← e.toTerm
          if e.height = 1 then
            return some (← `(term| $t:term))
          else
            return some (← `(term| $t:term)))
      args.foldlM (init := fn) (fun acc t => `($acc:term $t:term))
  | .CallLambda body exps =>
    let fn ← body.toTerm
    exps.foldlM (init := fn) (fun acc e => do
      let t ← e.toTerm
      if e.height = 1 then
        `($acc:term $t:term)
      else
        `($acc:term ($t:term)))
  | .StructCtor _ fields =>
    -- For each field, make it a `structInstField`
    let fields ← fields.toArray.mapM (fun ⟨field, exp⟩ => do
      let fieldIdent ← field.toIdent
      let expTerm ← Exp.toTerm exp
      `(structInstField| $fieldIdent:ident := $expTerm ))
    `( { $fields:structInstField* } )

  | .EnumCtor dt variant data =>
    let i ← Ident.toIdent <| Name.mkStr dt variant
    let data := data.toArray
    let numDataVals := data.size
    let identAsTerm ← `($i:ident)

    -- Build up the application of the data elements to the constructor
    data.foldlM (init := identAsTerm) (fun acc ⟨i, e⟩ => do
      let i ← i.toIdent
      let e ← e.toTerm
      -- Verus tells us not to expect the data elements to be
      -- serialized in order, so we need to name them if there's more than one
      if numDataVals = 1 then
        `($acc ($e))
      else
        `($acc ($i:ident := $e:term)))

  | .TupleCtor _ data =>
    let es ← data.toArray.mapM (fun e => do
      let e ← e.toTerm
      `(term| $e:term))
    let prodmkIdent := mkIdent `Prod.mk
    let rec mkTuple (arr : Array Term) : CoreM Term :=
      match arr with
      | #[]  => `(Unit.unit)
      | #[e] => return e
      | es   => do
        let stx ← mkTuple (es.eraseIdxIfInBounds 0)
        `($prodmkIdent $(es[0]!) ($stx))
    mkTuple es

  | .Unary op e =>
    op.toTerm (← e.toTerm)

  | .Binary op lhs rhs =>
    let lhs ← lhs.toTerm
    let rhs ← rhs.toTerm
    let t ← op.toTerm lhs rhs
    -- dbg_trace s!"[Elab.lean]: Binary op: {op} with lhs: {lhs} and rhs: {rhs} to term: {t}"
    -- let t' : Term ← `(($t:term))
    -- dbg_trace (← Lean.PrettyPrinter.formatTerm t)
    `(($t:term))

  | .If cond b₁ b₂ =>
    -- dbg_trace s!"[Elab.lean]: .If case - cond: {cond}"
    -- Check if this is a match pattern (IsVariant condition with MatchBlock branches)
    match cond with
    | .Unary (UnaryOp.IsVariant _dt _variant) scrutinee =>
      -- dbg_trace s!"[Elab.lean]: Detected IsVariant pattern: {dt}.{variant}"
      try
        let matchArms ← collectMatchArmsFromIfChain e
        -- dbg_trace s!"[Elab.lean]: Collected {matchArms.size} match arms from if chain"
        -- dbg_trace s!"[Elab.lean]: Match arms: {matchArms}"

        -- Build proper match expression
        -- dbg_trace s!"[Elab.lean]: Generating match expression with {matchArms.size} arms"
        let scrutineeTerm ← scrutinee.toTerm
        -- dbg_trace s!"[Elab.lean]: Scrutinee term: {scrutineeTerm}"
        let alts : Array (TSyntax ``matchAlt) ← matchArms.mapM fun (pattern, body) =>
          `(matchAltExpr| | $pattern => $body)
        `(match $scrutineeTerm:term with $alts:matchAlt*)
      catch _ =>
        dbg_trace s!"[Elab.lean]: .If case: Error collecting match arms"
        -- Fallback to the original MatchBlock translation
        let cond ← cond.toTerm
        let b₁ ← b₁.toTerm
        let b₂ ← b₂.toTerm
        `(if $cond then $b₁ else $b₂)
    | _ =>
      -- Regular if-else (not a match pattern)
      -- dbg_trace s!"[Elab.lean]: Regular if-else (not IsVariant)"
      let cond ← cond.toTerm
      let b₁ ← b₁.toTerm
      let b₂ ← b₂.toTerm
      `(if $cond then $b₁ else $b₂)

  | .Bind bind exp =>
    let exp ← exp.toTerm
    bind.toTerm exp

  | .ArrayLiteral es =>
    let es ← es.toArray.mapM (fun e => do
      let e ← e.toTerm
      `(term| $e:term))
    `({ $es:term,* }) -- to avoid the reserved Lean array notation `(#[ $es:term,* ])

  | .MatchBlock (scrutinee, _typ) body =>
    let scrutineeTerm ← scrutinee.toTerm
    try
      let matchArms ← collectMatchArmsFromIfChain e
      -- dbg_trace s!"[Elab.lean]: Match arms: {matchArms}"
      let alts : Array (TSyntax ``matchAlt) ← matchArms.mapM fun (pattern, body) =>
        `(matchAltExpr| | $pattern => $body)
      `(match $scrutineeTerm:term with $alts:matchAlt*)
    catch _ =>
      dbg_trace s!"[Elab.lean]: .MatchBlock case: Error collecting match arms"
      -- Fallback to the original MatchBlock translation
      body.toTerm
/-   | .MatchBlock scrutinee body =>
    -- For now, use the original approach but cleaner
    -- Generate the if-else structure that compiles correctly
    body.toTerm -/

end /- mutual -/

def addToTacticOption (acc : Option (TSyntax `tactic)) (tac : TSyntax `tactic) : CoreM (TSyntax `tactic) := do
  match acc with
  | none => return tac
  | some acc => `(tactic| ($acc:tactic; $tac:tactic))

partial def Stm.toTerm (stm : Stm) : CoreM Term := do
  match stm with
  | .Assert _ =>
    `(term| skip)

  | .Assume e =>
    let _e ← e.toTerm
    `(term| skip)

  | .AssertBitVector _ _ens =>
    `(term| skip)

  | .AssertLean e =>
    let _e ← e.toTerm
    `(term| skip)

  | .Assign lhs lhsTy rhs _ =>
    let rhs ← rhs.toTerm
    match lhs.baseVar? with
    | some lhsName =>
      let _lhs ← lhsName.toIdent
      let _lhsTy ← lhsTy.toTerm
      `(term| $rhs)
    | none =>
      -- Lean elaboration currently handles assignment only for variable l-values.
      `(term| $rhs)

  | .DeadEnd stm => stm.toTerm

  | .Block stms =>
    let stms ← stms.toArray.mapM (fun s => do
      let s ← s.toTerm
      `(term| $s:term))

    let stms : Array (TSyntax `term) := stms.filter (fun tac =>
      match tac with
      | `(term| skip) => false
      | _ => true)
    if stms.size = 0 then
      `(term| skip)
    else
      stms.foldlM (start := 1) (init := stms[0]!) (fun acc s => do
      `($acc:term $s:term))

  | _ => `(term| skip)


partial def Stm.toTactic (stm : Stm) : CoreM (TSyntax `tactic) := do
  match stm with
  | .Assert _ =>
    /-
      Skip `Assert`s because they are always followed by an `Assume`.

      As of April 2025, Verus's design is driven by incremental SMT solving
      and the calculation of the weakest pre-condition. To accomplish this,
      Verus places `Assert`s into an `ExprX::AssertAssume` node, which is
      translated into the SST by adding an `Assert(e)` node, and then
      an `Assume(e)` node. The `Assert()` is translated into a command
      which is discharged by the SMT solver, while the `Assume()`
      is then used by the weakest pre-condition calculation to add `e`
      to the context.

      We don't want duplicates of `Assert()` and `Assume()` floating
      around, so we skip the `Assert()`s.
    -/
    --let e ← e.toTerm
    --`(tactic| have : $e := by verus)
    `(tactic| skip)

  | .Assume e =>
    let e ← e.toTerm
    `(tactic| have : $e := by verus)

  | .AssertBitVector _ ens =>
    -- TODO: Skipping requires
    match ens with
    | [] => `(tactic| skip) -- CC: Really, this should be an error
    | [e] =>
      let e ← e.toTerm
      `(tactic| have : $e := by verus)
    | (e :: es) =>
      let e ← e.toTerm
      let ens ← es.foldlM (init := e) (fun acc e => do
        let e ← e.toTerm
        `($acc:term ∧ $e:term))
      `(tactic| have : $ens := by verus)

  | .AssertLean e =>
    let e ← e.toTerm
    `(tactic| have : $e := by auto? )

  | .Assign lhs lhsTy rhs _ =>
    match lhs.baseVar? with
    | some lhsName =>
      let lhs ← lhsName.toIdent
      let lhsTy ← lhsTy.toTerm
      let rhs ← rhs.toTerm
      `(tactic| let $lhs : $lhsTy := $rhs)
    | none =>
      -- Lean elaboration currently handles assignment only for variable l-values.
      `(tactic| skip)

  | .DeadEnd stm => stm.toTactic

  | .Block stms =>
    let stms ← stms.toArray.mapM (fun s => do
      let s ← s.toTactic
      `(tactic| $s:tactic))

    -- Filter our those tactics that are trivial (`skip`)
    -- This is mainly due to us not implementing other branches here
    -- We explicitly type this new array to keep the syntax category
    let stms : Array (TSyntax `tactic) := stms.filter (fun tac =>
      match tac with
      | `(tactic| skip) => false
      | _ => true)

    `(tactic| ($stms:tactic*))

    -- CC: Alternate method with slightly less well-formatted parentheses
    /-
    match ← stms.foldlM (init := none) (fun acc stm => do
      let tac ← stm.toTerm
      return some <| ← addToTacticOption acc tac
    ) with
    | none => `(tactic| skip)
    | some tac => return tac -/

  | _ => `(tactic| skip)


private def makeTypeBinders (as : Array String) : CoreM (TSyntaxArray ``bracketedBinder) := do
  Prod.fst <$> as.foldlM (init := (#[], 1)) (fun (arr, c) a => do
    let a ← a.toIdent
    let u ← String.toIdent s!"u{c}"
    let binder ← `(bracketedBinderF| ($a:ident : Type $u))
    return (arr.push binder, c + 1))

private def makeArrows (exps : Array Exp) : CoreM (TSyntax `term) := do
  if h : exps.size = 0 then
    -- let t ← `($(Syntax.mkCApp ``True #[]))
    -- dbg_trace (← Lean.PrettyPrinter.formatTerm t)
    `($TrueIdent)
  else
    let e ← Exp.toTerm exps[0]
    exps.foldlM (start := 1) (init := e) (fun acc e => do
      let e ← e.toTerm
      `($acc:term → $e:term))

private def makeAnds (exps : Array Exp) : CoreM (TSyntax `term) := do
  if h : exps.size = 0 then
    `($(Syntax.mkCApp ``True #[]))
  else
    let e ← Exp.toTerm exps[0]
    exps.foldlM (start := 1) (init := e) (fun acc e => do
      let e ← e.toTerm
      `($acc:term ∧ $e:term))

def Assertion.toCommand (a : Assertion) : CoreM (TSyntax `command) := do
  let ⟨name, decls, body⟩ := a
  let ident ← name.toIdent
  let args ← makeBracketedBinders decls.toArray
  let eTerm ← body.toTerm
  `(command| theorem $ident $args:bracketedBinder* : $eTerm := by auto? )

def SpecFn.toCommand (f : SpecFn) : CoreM (TSyntax `command) := do
  let ⟨name, inputs, returnType, decreases, body⟩ := f
  let ident ← name.toIdent
  let args ← makeBracketedBinders inputs.toArray
  let returnType ← returnType.toTerm
  let body ← body.toTerm
  match decreases with
  | none =>
    `(command| def $ident $args:bracketedBinder* : $returnType := $body )
  | some decreases =>
    let dec ← decreases.toTerm
    `(command| def $ident $args:bracketedBinder* : $returnType := $body
        termination_by $dec)

def ProofFn.toCommand (f : ProofFn) : CoreM (TSyntax `command) := do
  let ⟨name, inputs, requires, ensures, body, _locals⟩ := f
  let ident ← name.toIdent
  let args ← makeBracketedBinders inputs.toArray
  let _ ← -- Currently we ignore the proof body if the whole proof function is marked with `by(lean)`
    match body with
    | none => `(tactic| verus)
    | some body => body.toTactic
  let premises ← makeArrows requires.toArray
  let conclusions ← makeAnds ensures.toArray
  `(command| theorem $ident $args:bracketedBinder* : $premises → ($conclusions) := by
      auto? )

def ExecFn.toCommand (f : ExecFn) : CoreM (TSyntax `command) := do
  let ⟨name, inputs, _retName, returnType, _requires, _ensures, _body, _locals⟩ := f
  let ident ← name.toIdent
  let args ← makeBracketedBinders inputs.toArray
  let returnType ← returnType.toTerm
  `(command| opaque $ident $args:bracketedBinder* : $returnType)

def Struct.toCommand (s : Struct) : CoreM (TSyntax `command) := do
  let ⟨name, params, fields⟩ := s
  let nameAsIdent ← name.toIdent
  let params ← makeTypeBinders params.toArray
  let fields ← fields.toArray.mapM
    (fun ⟨fieldName, fieldTy⟩ => do
      let field ← fieldName.toIdent
      let ty ← fieldTy.toTerm
      `(structSimpleBinder| $field:ident : $ty))
  `(command|
    structure $nameAsIdent:ident $params:bracketedBinder* where
      $fields:structSimpleBinder*
    deriving _root_.DecidableEq)


def Enum.toCommand (e : Enum) : CoreM (TSyntax `command) := do
  let ⟨name, params, fields⟩ := e
  let nameAsIdent ← name.toIdent
  let params ← makeTypeBinders params.toArray
  let fields ← fields.toArray.mapM
    (fun field => do
      match field with
      | .labeled variantName data => do
        let variant ← variantName.toIdent
        let binders ← makeBracketedBinders data.toArray
        `(ctor| | $variant:ident $binders:bracketedBinder* )
      | .tuple variantName data => do
        let variant ← variantName.toIdent
        let arrows ← data.foldrM (init := nameAsIdent) (fun ty acc => do
          let ty ← ty.toTerm
          `($ty → $acc:term))
        `(ctor| | $variant:ident : $arrows ))
  `(command|
    inductive $nameAsIdent:ident $params:bracketedBinder* where
      $fields:ctor*
    deriving _root_.DecidableEq)


def FuncCheckSst.toCommand (f : FuncCheckSst) : CoreM (TSyntax `command) := do
  let ⟨name, reqs, enss, decls⟩ := f
  let ident ← name.toIdent
  let reqs : Array Term ← reqs.toArray.mapM (·.toTerm)
  let enss : Array Term ← enss.toArray.mapM (·.toTerm)
  let init : Term := trueIdent
  let req : Term ← reqs.foldlM (init := init) (fun acc e => `($acc && ($e)))
  let ens : Term ← enss.foldlM (init := init) (fun acc e => `($acc && ($e)))
  let body ← `( $req → $ens )
  let args ← makeBracketedBinders decls.toArray
  `(command| theorem $ident $args:bracketedBinder* : $body := by auto? )


mutual

partial def mutualBlockToCommand (ds : List Decl) : CoreM (TSyntax `command) := do
  let decls : List Command ← ds.mapM Decl.toTerm
/-
  let first : Command := decls[0]!
  let rest : List Command := decls.tail
  let commands : Command := rest.foldlM (init := first)
    (fun acc t =>
    `($acc:command
    $t:command)) -/
  let commands ← decls.toArray.mapM (fun d => do
    `(command| $d:command))
  `(command|
    mutual
    $commands:command*
    end)

partial def Decl.toTerm (d : Decl) : CoreM (TSyntax `command) := do
  match d with
  | .assertion a => a.toCommand
  | .specFn f => f.toCommand
  | .proofFn f => f.toCommand
  | .execFn f => f.toCommand
  | .struct s => s.toCommand
  | .enum e => e.toCommand
  | .func f => f.toCommand
  | .mutualBlock ds => mutualBlockToCommand ds

end /- mutual -/

end VerusLean
