/-
  Boole.Inference — VLIR-level type and bit-width inference helpers.

  Pure inspection over `Exp` / `Typ` / `VarEnv` (no `BuildM`, no BooleDDM
  emission). Used by the translator to decide bit-width promotions,
  comparison argument types, and numeric-kind classification before
  lowering. Splitting these out of `Translate.lean` keeps the inference
  metric-policy together and lets callers be reasoned about without
  pulling in the BooleDDM emit machinery.
-/
import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Signatures

namespace VerusLean.Boole.Inference

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.Names
open VerusLean.Boole.Signatures

/-! ## Variable Environments -/

abbrev VarEnv := Std.HashMap String Typ
abbrev BoundEnv := List (String × Typ)

/-- Per-`execFn` map: callee name → list of `&mut` parameter slots.
    Captured during decl collection so call-site translation can
    rewrite `f(..., &mut x, ...)` into `(out, ...) := f(..., x, ...)`. -/
structure MutArgInfo where
  idx : Nat
  ty : Typ

abbrev MutArgMap := Std.HashMap String (List MutArgInfo)

/-- Per-translation map from spec-fn name to its full `SpecFn` decl.
    Used by reveal lowering to inline a spec fn's body where its
    `reveal(...)` statement appeared. -/
abbrev SpecFnMap := Std.HashMap Ident SpecFn

def boundType? (bound : BoundEnv) (name : String) : Option Typ :=
  (bound.find? (fun (n, _) => n == name)).map Prod.snd

/-! ## Function-Type Lookup Keys

    Function return / parameter types are stored in `VarEnv` under
    namespaced keys so a single `Std.HashMap String Typ` can carry both
    variable-name → type and function-name → type information without
    name collisions. -/

def fnRetKey (fname : String) : String :=
  s!"__verus_fnret__{fname}"

def fnParamKey (fname : String) (idx : Nat) : String :=
  s!"__verus_fnparam__{fname}__{idx}"

def lookupFnRetType (env : VarEnv) (fname : String) : Option Typ :=
  env.get? (fnRetKey fname)

def lookupFnParamType (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  env.get? (fnParamKey fname idx)

/-- Combined lookup: prefer the per-translation env, fall back to the
    static known-signatures table from `Signatures.lean`. -/
def lookupFnRetTypeFull (env : VarEnv) (fname : String) : Option Typ :=
  lookupFnRetType env fname <|> lookupKnownFnRetType fname

def lookupFnParamTypeFull (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  lookupFnParamType env fname idx <|> lookupKnownFnParamType fname idx

/-! ## No-Parameter Function Markers

    Verus eta-encodes no-parameter spec fn calls with a sentinel
    `Box(Int(0))` argument. We record which fn names have no source
    parameters under a sentinel key in `VarEnv`, so the call-site
    translator can strip the sentinel argument before lowering. -/

def noParamMarkerKey (fname : String) : String :=
  s!"__verus_noparam_fn__{fname}"

def addNoParamFnMarkers (env : VarEnv) (noParamFns : List String) : VarEnv :=
  noParamFns.foldl (init := env) (fun acc fname => acc.insert (noParamMarkerKey fname) .Bool)

def hasNoParamFnMarker (env : VarEnv) (fname : String) : Bool :=
  env.contains (noParamMarkerKey fname)

/-! ## Mutable-Reference Helpers -/

def mutRefPayload? : Typ → Option Typ
  | .Decorated .MutRef ty => some ty
  | .Decorated _ ty => mutRefPayload? ty
  | _ => none

def mutArgInfos (inputs : List (String × Typ)) : List MutArgInfo :=
  let rec go (i : Nat) (rest : List (String × Typ)) : List MutArgInfo :=
    match rest with
    | [] => []
    | (_, ty) :: tail =>
      let here := match mutRefPayload? ty with
        | some payload => [{ idx := i, ty := payload }]
        | none => []
      here ++ go (i + 1) tail
  go 0 inputs

/-! ## Type-Shape Helpers -/

def isSeqTyp : Typ → Bool
  | .Struct name _ => datatypeNameOf name == "Seq"
  | .Decorated _ ty => isSeqTyp ty
  | _ => false

def vecElemTyp? : Typ → Option Typ
  | .Struct name params =>
    if isVecTypeName name then params.head? else none
  | .Decorated _ ty => vecElemTyp? ty
  | _ => none

def seqElemTyp? : Typ → Option Typ
  | .Struct name params =>
    match params with
    | elem :: _ => if datatypeNameOf name == "Seq" then some elem else none
    | [] => none
  | .Decorated _ ty => seqElemTyp? ty
  | _ => none

def arrayElemTyp? : Typ → Option Typ
  | .Array elem _ => some elem
  | .Decorated _ ty => arrayElemTyp? ty
  | _ => none

def arrayLen? : Typ → Option Nat
  | .Array _ len? => len?
  | .Decorated _ ty => arrayLen? ty
  | _ => none

def isFixedArrayTyp : Typ → Bool
  | .Array _ (some _) => true
  | .Decorated _ ty => isFixedArrayTyp ty
  | _ => false

def setElemTyp? : Typ → Option Typ
  | .Struct name params =>
    match params with
    | elem :: _ => if datatypeNameOf name == "Set" then some elem else none
    | [] => none
  | .Decorated _ ty => setElemTyp? ty
  | _ => none

/-- Pull out the first type parameter of an `expected?` `Struct` /
    `Decorated` type. Used to thread per-element types into sequence /
    array literal lowering when the surrounding context already knows
    the container type. -/
def firstStructParamFromExpected? : Option Typ → Option Typ
  | some (.Struct _ params) => params.head?
  | some (.Decorated _ ty) => firstStructParamFromExpected? (some ty)
  | _ => none

def rangeIndexTypFromExpected? : Option Typ → Option Typ
  | some (.Struct n params) =>
    if isRangeTypeName n then params.head? else none
  | some (.Decorated _ ty) => rangeIndexTypFromExpected? (some ty)
  | _ => none

/-- Recognise a `Range::Range`-shaped struct ctor field list
    (`[("start", _), ("end", _)]`) so the translator can lower it to
    a `Range_int` builder call instead of a generic struct ctor. -/
def isRangeCtorFields (fields : List (String × Exp)) : Bool :=
  match fields with
  | [("start", _), ("end", _)] => true
  | _ => false

/-- Expected type for `s.field` on a struct: looks up the destructor's
    return type via `lookupFnRetTypeFull`. -/
def structFieldExpectedType? (env : VarEnv) (dt : Ident) (field : String) : Option Typ :=
  let projField := projFieldNameOf dt (datatypeNameOf dt) field
  lookupFnRetTypeFull env (datatypeDestructorNameOf dt projField)

/-- Expected type for `e.field` under a known enum variant — same as
    `structFieldExpectedType?` but parameterised by the variant. -/
def enumFieldExpectedType? (env : VarEnv) (dt : Ident) (variant : String)
    (field : String) : Option Typ :=
  let projField := projFieldNameOf dt variant field
  lookupFnRetTypeFull env (datatypeDestructorNameOf dt projField)

/-- Encode a literal `seq![a, b, c]` as a folded `Seq_push` chain over
    `Seq_empty`. Pure construction; no `BuildM` because the prelude
    function names resolve at emission time. -/
def mkSeqLiteralExp (elems : List Exp) : Exp :=
  let mkPreludeName (name : String) : Ident := .str .anonymous name
  let seqEmpty : Exp := .Call (.Fun (mkPreludeName "Seq_empty")) [] []
  elems.foldl (init := seqEmpty) (fun acc elem =>
    .Call (.Fun (mkPreludeName "Seq_push")) [] [acc, elem])

/-- Peel `Box`/`Unbox`/`Clip`/`MatchBlock` wrappers around an
    `ArrayLiteral` to recover the underlying element list, if any.
    Used by `view(arr![...])` recognition. -/
partial def arrayLiteralElemsFromViewArg? : Exp → Option (List Exp)
  | .ArrayLiteral elems => some elems
  | .Unary op e =>
    match op with
    | .Box _ | .Unbox _ | .Clip _ _ | .Old | .Trigger | .HasType _ =>
      arrayLiteralElemsFromViewArg? e
    | _ => none
  | .Call fn _ [arg] =>
    if isViewName (CallFun.name fn) || isBoxNewName (CallFun.name fn) ||
        isArrayAsSliceName (CallFun.name fn) || isSliceIntoVecName (CallFun.name fn) then
      arrayLiteralElemsFromViewArg? arg
    else
      none
  | .MatchBlock _ body => arrayLiteralElemsFromViewArg? body
  | _ => none

/-! ## Expression Shape Helpers -/

partial def vecVarFromExp : Exp → Option String
  | .Var x => some x
  | .Unary op e =>
    match op with
    | .Box _ | .Unbox _ | .Clip _ _ | .Old | .Trigger | .HasType _ => vecVarFromExp e
    | _ => none
  | .Call fn _ [arg] =>
    if isViewName (CallFun.name fn) then vecVarFromExp arg else none
  | _ => none

def unwrapViewCall : Exp → Exp
  | .Call fn _ [inner] =>
    if isViewName (CallFun.name fn) then inner else .Call fn [] [inner]
  | e => e

/-! ## Bit-width Inference -/

def constIntExprVal? : Exp → Option Int
  | .Const (.Int i) _ => some i
  | .Binary (.Arith .Add _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l + r)
  | .Binary (.Arith .Sub _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l - r)
  | .Binary (.Arith .Mul _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l * r)
  | _ => none

def intFitsBitWidth (w : Nat) (signed : Bool) (i : Int) : Bool :=
  if signed then
    let lo : Int := -((2 : Int) ^ (w - 1))
    let hi : Int := (2 : Int) ^ (w - 1)
    lo <= i && i < hi
  else
    let hi : Int := (2 : Int) ^ w
    0 <= i && i < hi

partial def exprFitsBitWidth (w : Nat) (signed : Bool) : Exp → Bool
  | e =>
    match constIntExprVal? e with
    | some i => intFitsBitWidth w signed i
    | none =>
      match e with
      | .If _ t f => exprFitsBitWidth w signed t && exprFitsBitWidth w signed f
      | _ => false

def choosePromotedWidthForExpr?
    (fromW : Nat) (signed : Bool) (e : Exp) : Option Nat :=
  if !isSupportedBvWidth fromW then none
  else (supportedBvWidths.filter (fromW <= ·)).find? (exprFitsBitWidth · signed e)

def chooseBitArgTyForCmp
    (lhs rhs : Exp) (lhsInfo? rhsInfo? : Option (Nat × Bool)) : Option Typ :=
  match lhsInfo?, rhsInfo? with
  | some i1, some i2 =>
    (chooseBitPromotionInfo? i1 i2).map (fun (w, signed) => bitTypOfInfo w signed)
  | some (w, s), none =>
    (choosePromotedWidthForExpr? w s rhs).map (fun w' => bitTypOfInfo w' s)
  | none, some (w, s) =>
    (choosePromotedWidthForExpr? w s lhs).map (fun w' => bitTypOfInfo w' s)
  | none, none => none

/-- Infer bitwidth/signedness for an expression. -/
def inferBitInfo (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option (Nat × Bool) :=
  match e with
  | .Var x =>
    (boundType? bound x <|> env.get? x) |>.bind bitInfoOfTyp
  | .Call fn _ args =>
    let name := CallFun.name fn
    if isSliceLenSpecName name || isSliceLenExecName name then
      -- `slice::len` lowers to `Sequence.length(slice)` (int) at the
      -- call site, same as `Vec::len` / `Seq::len`.  Returning `none`
      -- here lets `comparisonPrelude` correctly fall back to int when
      -- the other operand is bv (e.g. `k < blocks.len()` with `k : usize`).
      none
    else if isSeqLenSpecName name || isVecLenSpecName name || isVecLenExecName name then
      none
    else if isVecIndexSpecName name || isVecIndexExecName name then
      match args with
      | vArg :: _ =>
        match vecVarFromExp vArg with
        | some base => env.get? base |>.bind vecElemTyp? |>.bind bitInfoOfTyp
        | none => none
      | _ => none
    else
      let fnStr := identToBoole name
      (lookupFnRetTypeFull env fnStr).bind bitInfoOfTyp
  | .Unary (.BitNot (some w)) e =>
    inferBitInfo env bound e <|>
      (if isSupportedBvWidth w then some (w, false) else none)
  | .Unary (.Unbox t) e => bitInfoOfTyp t <|> inferBitInfo env bound e
  | .Unary (.Box t) e => bitInfoOfTyp t <|> inferBitInfo env bound e
  | .Unary (.Clip (.U w) _) _ =>
    let w := w.toNat
    if isSupportedBvWidth w then some (w, false) else none
  | .Unary (.Clip (.I w) _) _ =>
    let w := w.toNat
    if isSupportedBvWidth w then some (w, true) else none
  | .Binary (.Bitwise (.Shl w _) _) _ _ => if isSupportedBvWidth w then some (w, false) else none
  | .Binary (.Bitwise (.Shr w) _) _ _ => if isSupportedBvWidth w then some (w, false) else none
  | .Unary _ e => inferBitInfo env bound e
  | .Binary _ e1 e2 => inferBitInfo env bound e1 <|> inferBitInfo env bound e2
  | .If _ t f => inferBitInfo env bound t <|> inferBitInfo env bound f
  | _ => none

partial def inferComparableTyp? (env : VarEnv) (bound : BoundEnv) : Exp → Option Typ
  | .Var x => boundType? bound x <|> env.get? x
  | .Call fn _ args =>
    let name := CallFun.name fn
    if isSliceLenSpecName name || isSliceLenExecName name then
      -- `slice::len` lowers to `Sequence.length(slice)` (int).
      some .Int
    else if isSeqLenSpecName name || isVecLenSpecName name || isVecLenExecName name then
      some .Int
    else if isVecIndexSpecName name || isVecIndexExecName name then
      match args with
      | vArg :: _ =>
        match vecVarFromExp (unwrapViewCall vArg) with
        | some base => env.get? base |>.bind vecElemTyp?
        | none => none
      | _ => none
    else
      lookupFnRetTypeFull env (identToBoole name)
  | .Unary (.Box t) _ => some t
  | .Unary (.Unbox t) _ => some t
  | .Unary (.Proj dt variant field _ _) _ =>
    let projField := projFieldNameOf dt variant field
    lookupFnRetTypeFull env (datatypeDestructorNameOf dt projField)
  | .Unary (.Clip range _) _ =>
    match range with
    | .Int => some .Int  | .Nat => some .Nat
    | .U w => some (.UInt w.toNat)  | .I w => some (.SInt w.toNat)
    | .USize => some (.UInt usizeBitWidth)  | .ISize => some (.SInt usizeBitWidth)
    | .Char => some .Char
  | .If _ t f => inferComparableTyp? env bound t <|> inferComparableTyp? env bound f
  | .Bind (.Let _ _ _) body => inferComparableTyp? env bound body
  | _ => none

def inferNumKind (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option NumKind :=
  match inferBitInfo env bound e with
  | some (w, s) => some (.bv w s)
  | none =>
    match inferComparableTyp? env bound e with
    | some .Int => some .int
    | some .Nat => some .nat
    | _ =>
      match e with
      | .Const _ ty => numKindOfTyp? ty
      | _ => none

private structure ArithFootprint where
  hasMathInt : Bool := false
  hasBv : Bool := false
deriving Inhabited

private def ArithFootprint.ofNumKind : Option NumKind → ArithFootprint
  | some (.bv ..) => { hasBv := true }
  | some .int | some .nat => { hasMathInt := true }
  | none => {}

private def ArithFootprint.merge (lhs rhs : ArithFootprint) : ArithFootprint :=
  { hasMathInt := lhs.hasMathInt || rhs.hasMathInt
    hasBv := lhs.hasBv || rhs.hasBv }

private def ArithFootprint.isMixed (f : ArithFootprint) : Bool :=
  f.hasMathInt && f.hasBv

/-- Classify a source arithmetic tree for numeric-domain selection.

    This is deliberately source-AST based: variables keep their source type,
    and mixed math-int/bitvector arithmetic is recognized before translation
    commits to either Boole int operators or Boole bv operators.

    Integer / nat literals don't contribute to the footprint: Verus typically
    serializes literals with their *default* type (often `.Int`) even when
    the surrounding context constrains them to a bv width (e.g. `8 * x1`
    where `x1 : i8` should stay pure-bv).  A bv-typed literal still counts
    as bv — that's how the user expresses an intentional bv constant. -/
partial def arithFootprint (env : VarEnv) (bound : BoundEnv) : Exp → ArithFootprint
  | .Binary (.Arith _ _) lhs rhs =>
    (arithFootprint env bound lhs).merge (arithFootprint env bound rhs)
  | .Unary (.Box t) _ | .Unary (.Unbox t) _ =>
    ArithFootprint.ofNumKind (numKindOfTyp? t)
  | .Const _ t =>
    match numKindOfTyp? t with
    | some (.bv ..) => { hasBv := true }
    | _ => {}
  | e =>
    ArithFootprint.ofNumKind (inferNumKind env bound e)

/-- True when any arithmetic subtree combines mathematical integer/nat values
    with fixed-width bitvectors. Such arithmetic is lowered in Boole `int`
    space with explicit `bv*_to_int_*` casts on bv operands; pure bv
    arithmetic stays bv, and pure mathematical arithmetic stays int. -/
partial def expHasMixedIntBvArith (env : VarEnv) (bound : BoundEnv) : Exp → Bool
  | e@(.Binary (.Arith _ _) _ _) => (arithFootprint env bound e).isMixed
  | .Binary _ lhs rhs =>
    expHasMixedIntBvArith env bound lhs || expHasMixedIntBvArith env bound rhs
  | .Unary _ e => expHasMixedIntBvArith env bound e
  | .If c t f =>
    expHasMixedIntBvArith env bound c ||
    expHasMixedIntBvArith env bound t ||
    expHasMixedIntBvArith env bound f
  | .Bind bind body =>
    let bindHasMixed :=
      match bind with
      | .Let _ _ e => expHasMixedIntBvArith env bound e
      | .Quant _ _ triggers =>
        triggers.any (fun group => group.any (expHasMixedIntBvArith env bound))
      | .Lambda _ => false
    bindHasMixed || expHasMixedIntBvArith env bound body
  | .Call _ _ args | .CallLambda _ args | .TupleCtor _ args | .ArrayLiteral args =>
    args.any (expHasMixedIntBvArith env bound)
  | .StructCtor _ fields | .EnumCtor _ _ fields =>
    fields.any (fun (_, e) => expHasMixedIntBvArith env bound e)
  | .MatchBlock (scrutinee, _) body =>
    expHasMixedIntBvArith env bound scrutinee ||
    expHasMixedIntBvArith env bound body
  | _ => false

def inferComparisonNumKind (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option NumKind :=
  if expHasMixedIntBvArith env bound e then some .int else inferNumKind env bound e

def inferComparisonBitInfo (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option (Nat × Bool) :=
  if expHasMixedIntBvArith env bound e then none else inferBitInfo env bound e

end VerusLean.Boole.Inference
