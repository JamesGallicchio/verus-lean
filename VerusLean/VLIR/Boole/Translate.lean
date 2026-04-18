/-
  VLIR to BooleDDM Direct Translation

  Translates the Verus-Lean IR (VLIR) directly to BooleDDM AST,
  bypassing the intermediate Strata Core representation.

  This module produces `BExpr`/`BStmt`/`BCmd` nodes from Builder.lean.
  Name-to-index state lives in Boole.Context and is used because BooleDDM
  represents source variables with numeric bvar/fvar indices.
-/

import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Bld
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Cast
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.ForLoop
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Normalize
import VerusLean.VLIR.Boole.Signatures
import VerusLean.VLIR.Boole.SupportEmit

namespace VerusLean.Boole

namespace Translate

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Cast
open VerusLean.Boole.Coercions
open VerusLean.Boole.Emit
open VerusLean.Boole.ForLoop
open VerusLean.Boole.Names
open VerusLean.Boole.Normalize
open VerusLean.Boole.Signatures
open VerusLean.Boole.SupportEmit

-- `Boole.Bld` re-exports Builder symbols under a short prefix so Translate
-- can refer to them as `Bld.fvar`, `Bld.app`, etc. without `open`-ing
-- Builder directly (whose names collide with Lean builtins and BooleDDM
-- constructors inside `mutual` blocks).
open VerusLean.Boole.Bld

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩
private def noLabel : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none
private def someLabel (s : String) : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  ann (some (.label default (ann s)))

/-- Predicate passed to `Normalize.inlineTemps`: which call-function names
    are safe to inline through temp-assignment prefixes without changing
    semantics. This is the translator-side view of library-shape names —
    kept here so `Normalize.lean` stays independent of `Names.lean`. -/
private def isPureBooleBuiltinCallName (fn : Ident) : Bool :=
  isViewName fn || isVecLenSpecName fn || isVecLenExecName fn
    || isVecIndexSpecName fn || isVecIndexExecName fn

/-! ## Type Aliases -/

abbrev VarEnv := Std.HashMap String Typ
abbrev BoundEnv := List (String × Typ)

structure MutArgInfo where
  idx : Nat
  ty : Typ

abbrev MutArgMap := Std.HashMap String (List MutArgInfo)

/-! ## Environment Helpers -/

def envFromDecls (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := (∅ : VarEnv)) (fun acc (n, t) => acc.insert n t)

private def extendEnv (env : VarEnv) (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := env) (fun acc (n, t) => acc.insert n t)

def boundIndex? (bound : BoundEnv) (name : String) : Option Nat :=
  let rec go (i : Nat) (rest : BoundEnv) : Option Nat :=
    match rest with
    | [] => none
    | (n, _) :: tail => if n == name then some i else go (i + 1) tail
  go 0 bound

def boundType? (bound : BoundEnv) (name : String) : Option Typ :=
  (bound.find? (fun (n, _) => n == name)).map Prod.snd

private def noParamMarkerKey (fname : String) : String :=
  s!"__verus_noparam_fn__{fname}"

private def addNoParamFnMarkers (env : VarEnv) (noParamFns : List String) : VarEnv :=
  noParamFns.foldl (init := env) (fun acc fname => acc.insert (noParamMarkerKey fname) .Bool)

private def hasNoParamFnMarker (env : VarEnv) (fname : String) : Bool :=
  env.contains (noParamMarkerKey fname)

private def fnRetKey (fname : String) : String :=
  s!"__verus_fnret__{fname}"

private def fnParamKey (fname : String) (idx : Nat) : String :=
  s!"__verus_fnparam__{fname}__{idx}"

private def lookupFnRetType (env : VarEnv) (fname : String) : Option Typ :=
  env.get? (fnRetKey fname)

private def lookupFnParamType (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  env.get? (fnParamKey fname idx)

private def preludeIdent (name : String) : Ident :=
  .str .anonymous name

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

private def normalizeCallArgsForCallee (env : VarEnv) (fname : Ident) (args : List Exp) : List Exp :=
  let fnameStr := identToBoole fname
  let argsNoFuel := normalizeCallArgs args
  if hasNoParamFnMarker env fnameStr then
    argsNoFuel.filter (fun e =>
      match e with
      | .Unary (.Box .Int) (.Const (.Int 0) _) => false
      | _ => true)
  else
    argsNoFuel

/-! ## Type Translation -/

/-- Translate a VLIR type to a BooleDDM type. -/
partial def typToBooleType (ty : Typ) : BuildM BType :=
  match ty with
  | .Empty | .Unit => do
    let idx ← resolveFreeVar "Unit"
    pure (fvarTy idx)
  | .Tuple t1 t2 => do
    requireSupport .tuple
    let idx ← resolveFreeVar "Tuple"
    let a1 ← typToBooleType t1
    let a2 ← typToBooleType t2
    pure (fvarTy idx #[a1, a2])
  | .Bool => pure boolTy
  | .Int => pure intTy
  | .Nat => do
    requireSupport .nat
    let idx ← resolveFreeVar "nat"
    pure (fvarTy idx)
  | .UInt w | .SInt w =>
    if isSupportedBvWidth w then pure (bvTy w) else pure intTy
  | .Char => pure intTy
  | .StrSlice => pure strTy
  | .Array t => do
    let elemTy ← typToBooleType t
    pure (mapTy intTy elemTy)
  | .TypParam name => do
    let idx ← resolveFreeVar (sanitizeIdent name)
    pure (fvarTy idx)
  | .SpecFn params ret => do
    let retTy ← typToBooleType ret
    params.foldrM (fun p acc => do
      let pTy ← typToBooleType p
      pure (arrowTy pTy acc)) retTy
  | .Decorated _ inner => typToBooleType inner
  | .Struct name params =>
    if isVecTypeName name then
      match params with
      | t :: _ => do
        let idx ← resolveFreeVar "Vec"
        let elemTy ← typToBooleType t
        pure (fvarTy idx #[elemTy])
      | [] => do
        let idx ← resolveFreeVar "Vec"
        pure (fvarTy idx)
    else if datatypeNameOf name == "Seq" then
      match params with
      | t :: _ => do pure (seqTy (← typToBooleType t))
      | [] => do pure (seqTy unknownTy)
    else do
      let dtName := datatypeNameOf name
      let idx ← resolveFreeVar dtName
      let args ← params.toArray.mapM typToBooleType
      pure (fvarTy idx args)
  | .Enum name params => do
    let dtName := datatypeNameOf name
    let idx ← resolveFreeVar dtName
    let args ← params.toArray.mapM typToBooleType
    pure (fvarTy idx args)
  | .AirNamed str => do
    let idx ← resolveFreeVar str
    pure (fvarTy idx)

private def typToBooleTypeOrUnknown : Option Typ → BuildM BType
  | some ty => typToBooleType ty
  | none => pure unknownTy

def isSeqTyp : Typ → Bool
  | .Struct name _ => datatypeNameOf name == "Seq"
  | .Decorated _ ty => isSeqTyp ty
  | _ => false

def vecElemTyp? : Typ → Option Typ
  | .Struct name params =>
    if isVecTypeName name then params.head? else none
  | .Decorated _ ty => vecElemTyp? ty
  | _ => none

/-! ## Full lookups combining env + known functions -/

private def lookupFnRetTypeFull (env : VarEnv) (fname : String) : Option Typ :=
  lookupFnRetType env fname <|> lookupKnownFnRetType fname

private def lookupFnParamTypeFull (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  lookupFnParamType env fname idx <|> lookupKnownFnParamType fname idx

/-! ## Bit-width Inference -/

private def constIntExprVal? : Exp → Option Int
  | .Const (.Int i) _ => some i
  | .Binary (.Arith .Add _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l + r)
  | .Binary (.Arith .Sub _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l - r)
  | .Binary (.Arith .Mul _) lhs rhs => do
    let l ← constIntExprVal? lhs; let r ← constIntExprVal? rhs; some (l * r)
  | _ => none

private def intFitsBitWidth (w : Nat) (signed : Bool) (i : Int) : Bool :=
  if signed then
    let lo : Int := -((2 : Int) ^ (w - 1))
    let hi : Int := (2 : Int) ^ (w - 1)
    lo <= i && i < hi
  else
    let hi : Int := (2 : Int) ^ w
    0 <= i && i < hi

private partial def exprFitsBitWidth (w : Nat) (signed : Bool) : Exp → Bool
  | e =>
    match constIntExprVal? e with
    | some i => intFitsBitWidth w signed i
    | none =>
      match e with
      | .If _ t f => exprFitsBitWidth w signed t && exprFitsBitWidth w signed f
      | _ => false

private def choosePromotedWidthForExpr?
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

/-- Infer bitwidth/signedness for an expression. -/
def inferBitInfo (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option (Nat × Bool) :=
  match e with
  | .Var x =>
    (boundType? bound x <|> env.get? x) |>.bind bitInfoOfTyp
  | .Call fn _ args =>
    let name := CallFun.name fn
    if isVecLenSpecName name || isVecLenExecName name then
      some (usizeBitWidth, false)
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

private partial def inferComparableTyp? (env : VarEnv) (bound : BoundEnv) : Exp → Option Typ
  | .Var x => boundType? bound x <|> env.get? x
  | .Call fn _ args =>
    let name := CallFun.name fn
    if isVecLenSpecName name || isVecLenExecName name then
      some (.UInt usizeBitWidth)
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
    | _ => none

/-! ## Resolve Helpers -/

private def resolveVar (name : String) : BuildM BExpr := do
  let sanName := sanitizeVarName name
  match ← lookupBoundVar sanName with
  | some idx => pure (Bld.bvar idx)
  | none =>
    let idx ← resolveFreeVar sanName
    pure (Bld.fvar idx)

/-! ## Expression Translation -/

def constToBoole (expected? : Option Typ) : Const → BExpr
  | .Bool b => boolConst b
  | .Int i =>
    match expected?.bind bitWidthOfTyp with
    | some w => bitvecConstNat w (if i >= 0 then i.toNat else (BitVec.ofInt w i).toNat)
    | none => intConst i
  | .StrSlice s => .strLit default (ann s)
  | .Char c => intConst c.toNat

/-- Apply a binary bitvector operation. -/
private def applyBvBinOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "Add" => some (bvAdd w a b)
  | "Sub" => some (bvSub w a b)
  | "Mul" => some (bvMul w a b)
  | "UDiv" => some (bvUDiv w a b)
  | "UMod" => some (bvUMod w a b)
  | "SDiv" => some (bvSDiv w a b)
  | "SMod" => some (bvSMod w a b)
  | _ => none

/-- Apply a bitvector bitwise operation. -/
private def applyBvBitOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "And" => some (bvAnd w a b)
  | "Or" => some (bvOr w a b)
  | "Xor" => some (bvXor w a b)
  | "Shl" => some (bvShl w a b)
  | "UShr" => some (bvUShr w a b)
  | _ => none

/-- Apply a bitvector comparison operation. -/
private def applyBvCmpOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "ULt" => some (bvUlt w a b)
  | "ULe" => some (bvUle w a b)
  | "UGt" => some (bvUgt w a b)
  | "UGe" => some (bvUge w a b)
  | "SLt" => some (bvSlt w a b)
  | "SLe" => some (bvSle w a b)
  | "SGt" => some (bvSgt w a b)
  | "SGe" => some (bvSge w a b)
  | _ => none

private def applyBinaryOp (op : BinaryOp) (a b : BExpr) : Option BExpr :=
  match op with
  | .And => some (boolAnd a b)
  | .Or => some (boolOr a b)
  | .Implies => some (boolImplies a b)
  | .Arith .Add _ => some (intAdd a b)
  | .Arith .Sub _ => some (intSub a b)
  | .Arith .Mul _ => some (intMul a b)
  | .Arith .EuclideanDiv _ => some (intDiv a b)
  | .Arith .EuclideanMod _ => some (intMod a b)
  | .Inequality .Le => some (intLe a b)
  | .Inequality .Lt => some (intLt a b)
  | .Inequality .Ge => some (intGe a b)
  | .Inequality .Gt => some (intGt a b)
  | _ => none

private def applyUnaryOp (op : UnaryOp) (a : BExpr) : Option BExpr :=
  match op with
  | .Not => some (boolNot a)
  | _ => none

private def seqElemTyp? : Typ → Option Typ
  | .Struct name params =>
    match params with
    | elem :: _ => if datatypeNameOf name == "Seq" then some elem else none
    | [] => none
  | .Decorated _ ty => seqElemTyp? ty
  | _ => none

private def setElemTyp? : Typ → Option Typ
  | .Struct name params =>
    match params with
    | elem :: _ => if datatypeNameOf name == "Set" then some elem else none
    | [] => none
  | .Decorated _ ty => setElemTyp? ty
  | _ => none

private def firstStructParamFromExpected? : Option Typ → Option Typ
  | some (.Struct _ params) => params.head?
  | some (.Decorated _ ty) => firstStructParamFromExpected? (some ty)
  | _ => none

private def rangeIndexTypFromExpected? : Option Typ → Option Typ
  | some (.Struct n params) =>
    if isRangeTypeName n then params.head? else none
  | some (.Decorated _ ty) => rangeIndexTypFromExpected? (some ty)
  | _ => none

private def isRangeCtorFields (fields : List (String × Exp)) : Bool :=
  match fields with
  | [("start", _), ("end", _)] => true
  | _ => false

private def structFieldExpectedType? (env : VarEnv) (dt : Ident) (field : String) : Option Typ :=
  let projField := projFieldNameOf dt (datatypeNameOf dt) field
  lookupFnRetTypeFull env (datatypeDestructorNameOf dt projField)

private def enumFieldExpectedType? (env : VarEnv) (dt : Ident) (variant : String)
    (field : String) : Option Typ :=
  let projField := projFieldNameOf dt variant field
  lookupFnRetTypeFull env (datatypeDestructorNameOf dt projField)

private def mkSeqLiteralExp (elems : List Exp) : Exp :=
  let seqEmpty : Exp := .Call (.Fun (preludeIdent "Seq_empty")) [] []
  elems.foldl (init := seqEmpty) (fun acc elem =>
    .Call (.Fun (preludeIdent "Seq_push")) [] [acc, elem])

private partial def arrayLiteralElemsFromViewArg? : Exp → Option (List Exp)
  | .ArrayLiteral elems => some elems
  | .Unary op e =>
    match op with
    | .Box _ | .Unbox _ | .Clip _ _ | .Old | .Trigger | .HasType _ =>
      arrayLiteralElemsFromViewArg? e
    | _ => none
  | .MatchBlock _ body => arrayLiteralElemsFromViewArg? body
  | _ => none

/-! ## Statement Helpers -/

def sameExpShape (e1 e2 : Exp) : Bool := e1 == e2

def queryBodyStms : Stm → List Stm
  | .Block [s] => queryBodyStms s
  | .Block stms => stms
  | s => [s]

def takeLeadingAssumes : List Stm → List Exp × List Stm
  | (.Assume e) :: rest =>
    let (reqs, tail) := takeLeadingAssumes rest
    (e :: reqs, tail)
  | stms => ([], stms)

def takeLeadingEnsuresRev : List Stm → List Exp × List Stm
  | (.Assert e) :: rest | (.AssertLean e) :: rest =>
    let (ens, tail) := takeLeadingEnsuresRev rest
    (e :: ens, tail)
  | stms => ([], stms)

def queryReqEnsFromBody (body : Stm) : Option (List Exp × List Exp) :=
  let stms := (queryBodyStms body).map stripSingletonBlocks
  let (reqs, rest) := takeLeadingAssumes stms
  let (ensRev, _) := takeLeadingEnsuresRev rest.reverse
  let ens := ensRev.reverse
  if ens.isEmpty then none else some (reqs, ens)

def isQueryScaffoldingAssume (assumed : Exp) : Stm → Bool
  | .AssertBitVector _ ensures => ensures.any (fun e => sameExpShape e assumed)
  | .AssertQuery _ body =>
    match queryReqEnsFromBody body with
    | some (_, ensures) => ensures.any (fun e => sameExpShape e assumed)
    | none => false
  | _ => false

def isQueryStmt : Stm → Bool
  | .AssertBitVector _ _ => true
  | .AssertQuery _ _ => true
  | _ => false

def isTrivialTrueAssert : Stm → Bool
  | .Assert (.Const (.Bool true) _) => true
  | .AssertLean (.Const (.Bool true) _) => true
  | _ => false

def isAssertAssumeEcho (a : Stm) (assumed : Exp) : Bool :=
  match a with
  | .Assert e => sameExpShape e assumed
  | .AssertLean e => sameExpShape e assumed
  | _ => false

def assertQueryModeLabel : AssertQueryMode → String
  | .NonLinear => "nonlinear_query"
  | .BitVector => "bitvector_query"
  | .Other _ => "assert_query"

/-! ## Reveal Support -/

abbrev SpecFnMap := Std.HashMap Ident SpecFn

private partial def typTypeVars : Typ → List String
  | .TypParam n => [sanitizeIdent n]
  | .Tuple t1 t2 => (typTypeVars t1 ++ typTypeVars t2).eraseDups
  | .Array t => typTypeVars t
  | .SpecFn ps ret => ((ps.flatMap typTypeVars) ++ typTypeVars ret).eraseDups
  | .Decorated _ t => typTypeVars t
  | .Struct _ ps => (ps.flatMap typTypeVars).eraseDups
  | .Enum _ ps => (ps.flatMap typTypeVars).eraseDups
  | _ => []

private def specFnIsGenericFull (f : SpecFn) : Bool :=
  let inputTVars := f.inputs.flatMap (fun (_, ty) => typTypeVars ty)
  let retTVars := typTypeVars f.returnType
  !(inputTVars ++ retTVars).isEmpty

private def fnTypeParams (inputs : List (String × Typ)) (ret : Typ) : List String :=
  ((inputs.flatMap (fun (_, ty) => typTypeVars ty)) ++ typTypeVars ret).eraseDups

private def mkTypeArgsAnn (params : List String) :
    Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
  if params.isEmpty then
    ann none
  else
    let vars := params.toArray.map fun p =>
      BooleDDM.TypeVar.type_var default (ann p)
    ann (some (BooleDDM.TypeArgs.type_args default (ann vars)))

private def mkRevealAssume (f : SpecFn) : Option Stm :=
  if specFnIsGenericFull f then none
  else match f.body with
  | none => none
  | some body =>
    let callArgs := f.inputs.map (fun (x, _) => Exp.Var x)
    let call := Exp.Call (.Fun f.name) [] callArgs
    let eq := Exp.Binary (.Eq .Spec) call body
    let equation :=
      if f.inputs.isEmpty then eq
      else Exp.Bind (.Quant .Forall f.inputs []) eq
    some (.Assume equation)

partial def expandReveals (sfMap : SpecFnMap) : Stm → Stm
  | .Reveal fn _fuel =>
    match sfMap.get? fn with
    | some f => (mkRevealAssume f).getD (.Block [])
    | none => .Block []
  | .Block stms => .Block (stms.map (expandReveals sfMap))
  | .If cond b1 b2 =>
    .If cond (expandReveals sfMap b1) (b2.map (expandReveals sfMap))
  | .DeadEnd stm => .DeadEnd (expandReveals sfMap stm)
  | .OpenInvariant stm => .OpenInvariant (expandReveals sfMap stm)
  | .ClosureInner body => .ClosureInner (expandReveals sfMap body)
  | .AssertQuery mode body => .AssertQuery mode (expandReveals sfMap body)
  | .Loop isFor label cond body invs dec =>
    let cond' := cond.map (fun (s, e) => (expandReveals sfMap s, e))
    .Loop isFor label cond' (expandReveals sfMap body) invs dec
  | s => s

/-- Allocate a fresh synthetic loop label of the form `loop_N`, where `N`
    comes from `BuildCtx.loopLabelCounter`. Used when a `.Loop` has no
    source-level label but its body contains unlabeled `break`/`continue`
    that need a target — deriving the label from AST structure would
    risk collisions between structurally identical loops. -/
private def implicitLoopLabel : BuildM String := do
  let n ← freshLoopLabelId
  pure (sanitizeIdent s!"loop_{n}")

private partial def hasUnlabeledLoopControl : Stm → Bool
  | .BreakOrContinue none _ => true
  | .DeadEnd stm => hasUnlabeledLoopControl stm
  | .If _ b1 b2 =>
    hasUnlabeledLoopControl b1 || (b2.map hasUnlabeledLoopControl).getD false
  | .OpenInvariant stm => hasUnlabeledLoopControl stm
  | .ClosureInner body => hasUnlabeledLoopControl body
  | .AssertQuery _ body => hasUnlabeledLoopControl body
  | .Block stms => stms.any hasUnlabeledLoopControl
  | .Loop .. => false
  | _ => false

partial def bindUnlabeledLoopControlTo (loopLabel : String) : Stm → Stm
  | .BreakOrContinue none isBreak => .BreakOrContinue (some loopLabel) isBreak
  | .DeadEnd stm => .DeadEnd (bindUnlabeledLoopControlTo loopLabel stm)
  | .If cond b1 b2 =>
    .If cond (bindUnlabeledLoopControlTo loopLabel b1) (b2.map (bindUnlabeledLoopControlTo loopLabel))
  | .OpenInvariant stm => .OpenInvariant (bindUnlabeledLoopControlTo loopLabel stm)
  | .ClosureInner body => .ClosureInner (bindUnlabeledLoopControlTo loopLabel body)
  | .AssertQuery mode body => .AssertQuery mode (bindUnlabeledLoopControlTo loopLabel body)
  | .Block stms => .Block (stms.map (bindUnlabeledLoopControlTo loopLabel))
  | s@(.Loop ..) => s
  | s => s

/-! ## Expression Translation -/

mutual

private partial def comparisonPrelude
    (env : VarEnv) (bound : BoundEnv) (lhs rhs : Exp) :
    BuildM (Option Typ × BExpr × BExpr) := do
  let lhsInfo? := inferBitInfo env bound lhs
  let rhsInfo? := inferBitInfo env bound rhs
  let lhsNum? := inferNumKind env bound lhs
  let rhsNum? := inferNumKind env bound rhs
  let argTy? :=
    chooseBitArgTyForCmp lhs rhs lhsInfo? rhsInfo? <|>
    match lhsInfo?, rhsInfo?, lhsNum?, rhsNum? with
    | some (w, s), none, _, some .int
    | some (w, s), none, _, some .nat =>
      some (bitTypOfInfo w s)
    | none, some (w, s), some .int, _
    | none, some (w, s), some .nat, _ =>
      some (bitTypOfInfo w s)
    | _, _, _, _ => none
  let fallbackToInt := argTy?.isNone &&
    (lhsInfo?.isSome || rhsInfo?.isSome ||
     lhsNum? == some .nat || rhsNum? == some .nat)
  if fallbackToInt then
    let l0 ← expToBoole env bound none lhs
    let r0 ← expToBoole env bound none rhs
    let l ← coerceNumeric lhsNum? (some .int) l0
    let r ← coerceNumeric rhsNum? (some .int) r0
    return (argTy?, l, r)
  else
    -- Same narrow-then-widen gating as `.Binary` (see that site).
    let lExpected? := if lhsInfo?.isSome then none else argTy?
    let rExpected? := if rhsInfo?.isSome then none else argTy?
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let targetInfo? := argTy?.bind bitInfoOfTyp
    let l ← coerceBvBv lhsInfo? targetInfo? l0
    let r ← coerceBvBv rhsInfo? targetInfo? r0
    return (argTy?, l, r)

/-- Translate a VLIR expression to a BooleDDM expression. -/
partial def expToBoole (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) :
    Exp → BuildM BExpr
  | .Var x => do
    let actualTy? := boundType? bound x <|> env.get? x
    let e ← resolveVar x
    let srcKind? := actualTy?.bind numKindOfTyp?
    let tgtKind? := expected?.bind numKindOfTyp?
    coerceNumeric srcKind? tgtKind? e
  | .Const c ty =>
    -- Caller-provided `expected?` wins (it knows the surrounding context,
    -- e.g. a shift-amount that must match the LHS width even when the
    -- literal's source typ is narrower). Fall back to the Const's own
    -- VLIR typ when it pins down a bv width — this preserves
    -- source-declared widths (e.g. `1u32`) in contexts where `expected?`
    -- couldn't propagate, such as inside a `.Binary` whose own type
    -- inference was inconclusive (mixed-sign operands).
    let effectiveTy? :=
      expected? <|>
        (if (bitWidthOfTyp ty).isSome then some ty else none)
    return constToBoole effectiveTy? c
  | .StructCtor dt fields => do
    let ctorIdx ← resolveFreeVar (structCtorNameOf dt)
    let ctor := Bld.fvar ctorIdx
    let args ← fields.mapM (fun (field, e) => do
      let fieldExpected? :=
        if isRangeTypeName dt || isRangeCtorFields fields then
          rangeIndexTypFromExpected? expected? <|>
            firstStructParamFromExpected? expected? <|>
            structFieldExpectedType? env dt field
        else
          structFieldExpectedType? env dt field
      expToBoole env bound fieldExpected? e)
    return Bld.appN ctor args
  | .EnumCtor dt variant data => do
    let ctorIdx ← resolveFreeVar (enumCtorNameOf dt variant)
    let ctor := Bld.fvar ctorIdx
    let args ← data.mapM (fun (field, e) =>
      expToBoole env bound (enumFieldExpectedType? env dt variant field) e)
    return Bld.appN ctor args
  | .TupleCtor size data => do
    if size == 2 then requireSupport .tuple
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let ctor := Bld.fvar ctorIdx
    let args ← data.mapM (expToBoole env bound none)
    return Bld.appN ctor args
  | .Binary (.ExtEq deep ty) lhs rhs => do
    extEqExpToBoole env bound deep ty lhs rhs
  | .Binary (.Eq _) lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    let argTy ← typToBooleTypeOrUnknown argTy?
    return Bld.eqTyped argTy l r
  | .Binary .Ne lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    let argTy ← typToBooleTypeOrUnknown argTy?
    return Bld.neqTyped argTy l r
  | .Binary .Xor lhs rhs => do
    let l ← expToBoole env bound none lhs
    let r ← expToBoole env bound none rhs
    return boolNot (boolEquiv l r)
  | .Binary (.Inequality cmp) lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    match argTy? with
    | some ty =>
      match bitInfoOfTyp ty with
      | some (w, signed) =>
        let opName := match cmp with
          | .Le => if signed then "SLe" else "ULe"
          | .Lt => if signed then "SLt" else "ULt"
          | .Ge => if signed then "SGe" else "UGe"
          | .Gt => if signed then "SGt" else "UGt"
        match applyBvCmpOp w opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        throw s!"internal error: expected bitvector comparison type, got {repr ty}"
    | none =>
      match cmp with
      | .Le => return intLe l r
      | .Lt => return intLt l r
      | .Ge => return intGe l r
      | .Gt => return intGt l r
  | .Binary op lhs rhs => do
    let lhsInfo? := inferBitInfo env bound lhs
    let rhsInfo? := inferBitInfo env bound rhs
    let hasMixedSignedBitArgs :=
      match lhsInfo?, rhsInfo? with
      | some (_, s1), some (_, s2) => s1 != s2
      | _, _ => false
    let baseInfo? :=
      match lhsInfo?, rhsInfo? with
      | some i1, some i2 => chooseBitPromotionInfo? i1 i2
      | some info, none => some info
      | none, some info => some info
      | none, none => none
    let info? :=
      match baseInfo?, expected?.bind bitInfoOfTyp with
      | some (bw, bs), some (ew, es) =>
        if bs == es && canPromoteBvWidths bw ew then some (ew, es) else some (bw, bs)
      | some b, none => some b
      | none, some e =>
        if hasMixedSignedBitArgs then none else some e
      | none, none => none
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    -- Preserve narrow-then-widen for Verus's bit-vector proof mode: only
    -- push `argTy?` when the operand has no natural bv width of its own
    -- (e.g. a literal). See `bitvector_basic::test10` for the failure mode.
    let lExpected? := if lhsInfo?.isSome then none else argTy?
    let rExpected? := if rhsInfo?.isSome then none else argTy?
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let l ← coerceBvBv lhsInfo? info? l0
    let r ← coerceBvBv rhsInfo? info? r0
    match op with
    | .Bitwise bitop _ =>
      let w? := match bitop with
        | .Shl w _ | .Shr w => some w
        | _ => info?.map Prod.fst
      let signed := info?.map Prod.snd |>.getD false
      let opName := match bitop with
        | .BitAnd => "And"
        | .BitOr => "Or"
        | .BitXor => "Xor"
        | .Shl _ _ => "Shl"
        | .Shr _ => if signed then "SShr" else "UShr"
      let resolvedW := w?.getD usizeBitWidth
      match opName with
      | "SShr" =>
        -- Signed shift right: no direct builder, fall through to fvar
        let fnIdx ← resolveFreeVar s!"Bv{resolvedW}.SShr"
        return Bld.appN (Bld.fvar fnIdx) [l, r]
      | _ =>
        match applyBvBitOp resolvedW opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {resolvedW} for op {opName}"
    | .Arith a _ =>
      match info? with
      | some (w, signed) =>
        let opName := match a with
          | .Add => "Add"
          | .Sub => "Sub"
          | .Mul => "Mul"
          | .EuclideanDiv => if signed then "SDiv" else "UDiv"
          | .EuclideanMod => if signed then "SMod" else "UMod"
        match applyBvBinOp w opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        match applyBinaryOp op l r with
        | some result => return result
        | none => throw s!"unsupported binary op: {repr op}"
    | _ =>
      match applyBinaryOp op l r with
      | some result => return result
      | none => throw s!"unsupported binary op: {repr op}"
  | .Unary op e => do
    let x ←
      match op with
      | .Clip (.U w) _ =>
        let targetW := w.toNat
        let innerInfo? := inferBitInfo env bound e
        let isWidening := match innerInfo? with
          | some (iw, _) => decide (iw < targetW) | none => false
        let hint? := if isWidening then
          innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
        else
          some (.UInt targetW)
        let x0 ← expToBoole env bound hint? e
        if isSupportedBvWidth targetW then
          coerceBvBv innerInfo? (some (targetW, false)) x0
        else
          pure x0
      | .Clip (.I w) _ =>
        let targetW := w.toNat
        let innerInfo? := inferBitInfo env bound e
        let isWidening := match innerInfo? with
          | some (iw, _) => decide (iw < targetW) | none => false
        let hint? := if isWidening then
          innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
        else
          some (.SInt targetW)
        let x0 ← expToBoole env bound hint? e
        if isSupportedBvWidth targetW then
          coerceBvBv innerInfo? (some (targetW, true)) x0
        else
          pure x0
      | .Clip .Nat _ =>
        expToBoole env bound (some .Nat) e
      | .Box t => do
        let inner ← expToBoole env bound (some t) e
        let srcKind? := numKindOfTyp? t
        let tgtKind? := expected?.bind numKindOfTyp?
        coerceNumeric srcKind? tgtKind? inner
      | .BitNot w? =>
        let srcInfo? := inferBitInfo env bound e
        let annotFallback := w?.bind (fun w0 =>
          if isSupportedBvWidth w0 then some (w0, false) else none)
        let targetInfo? := expected?.bind bitInfoOfTyp <|> srcInfo? <|> annotFallback
        let innerExpected? :=
          if srcInfo?.isSome then none
          else targetInfo?.map (fun (w, signed) => bitTypOfInfo w signed)
        expToBoole env bound innerExpected? e
      | _ => expToBoole env bound expected? e
    match op with
    | .Clip _ _ => return x
    | .BitNot w? =>
      let srcInfo? := inferBitInfo env bound e
      let annotFallback := w?.bind (fun w0 =>
        if isSupportedBvWidth w0 then some (w0, false) else none)
      let targetInfo? := expected?.bind bitInfoOfTyp <|> srcInfo? <|> annotFallback
      match targetInfo?.map Prod.fst with
      | some w =>
        let x' ← coerceBvBv srcInfo? targetInfo? x
        return bvNot w x'
      | none => throw "missing bitvector width for op Not"
    | .Old =>
      -- Strata's `old` refers to a pre-state snapshot registered via
      -- `modifies` clauses — we don't emit those, and doing so correctly
      -- would need a wider redesign. Fortunately stripping `.Old` at
      -- emission is semantics-preserving for our pipeline:
      --   • Owned params are immutable in Boole, so `old(p) == p`.
      --   • `&mut` params are modeled via an explicit `_out` rename on the
      --     ensures (see `execFnToBoole`); `substExp` deliberately does not
      --     recurse into `.Unary .Old` bodies (see `Normalize.substExp`),
      --     so the name inside `.Old` keeps pointing at the original input
      --     — i.e. the pre-state value.
      -- In both cases the correct Boole expression is the inner one.
      return x
    | .Trigger => return x
    | .Box _ => return x
    | .Unbox _ => return x
    | .HasType _ => return x
    | .Proj dt variant field _getVariant check => do
      if check == .Yes then
        throw s!"unsupported checked field projection: {dt}::{variant}.{field}"
      let projField := projFieldNameOf dt variant field
      let projIdx ← resolveFreeVar (datatypeDestructorNameOf dt projField)
      return Bld.app (Bld.fvar projIdx) x
    | .IsVariant dt variant => do
      let testerIdx ← resolveFreeVar (enumTesterNameOf dt variant)
      return Bld.app (Bld.fvar testerIdx) x
    | .Proj' size field => do
      let projName ←
        if size == 2 then do
          requireSupport .tuple
          pure s!"Tuple.._{field}"
        else
          pure s!"Tuple_{size}_{field}"
      let projIdx ← resolveFreeVar projName
      return Bld.app (Bld.fvar projIdx) x
    | _ =>
      match applyUnaryOp op x with
      | some result => return result
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToBoole env bound (some .Bool) c
    let t' ← expToBoole env bound expected? t
    let e' ← expToBoole env bound expected? e
    let resultTy ← typToBooleTypeOrUnknown expected?
    return Bld.iteTyped resultTy c' t' e'
  | .Call fn _typs args => do
    let fname := CallFun.name fn
    let fnameStr := identToBoole fname
    let argsFiltered := normalizeCallArgsForCallee env fname args
    -- Seq built-in helper
    let mkSeqBuiltinCall (opName : String) (argSpecs : List (Exp × Option Typ)) := do
      let args' ← argSpecs.mapM (fun (arg, ty?) => expToBoole env bound ty? arg)
      let fnIdx ← resolveFreeVar s!"Sequence.{opName}"
      return Bld.appN (Bld.fvar fnIdx) args'
    let mkFallback := do
      let args' ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
        let paramTy? := lookupFnParamTypeFull env fnameStr idx
        let argExpected? := paramTy? <|> (match expected? with
          | some ty => if isIntTyp ty then some Typ.Int else none
          | none => none)
        expToBoole env bound argExpected? arg)
      let fnIdx ← resolveFreeVar fnameStr
      return Bld.appN (Bld.fvar fnIdx) args'
    if isViewName fname then
      match argsFiltered with
      | [arg] =>
        match vecVarFromExp arg with
        | some _base =>
          match env.get? _base |>.bind vecElemTyp? with
          | some _ =>
            let vecExpr ← expToBoole env bound none arg
            let viewIdx ← resolveFreeVar "Vec_view"
            return Bld.app (Bld.fvar viewIdx) vecExpr
          | none => expToBoole env bound expected? arg
        | none =>
          match expected? with
          | some ty =>
            if isSeqTyp ty then
              match arrayLiteralElemsFromViewArg? arg with
              | some elems => expToBoole env bound expected? (.ArrayLiteral elems)
              | none => expToBoole env bound expected? arg
            else expToBoole env bound expected? arg
          | none => expToBoole env bound expected? arg
      | _ => mkFallback
    else if isVecLenSpecName fname || isVecLenExecName fname then
      match argsFiltered with
      | [arg] =>
        let vecExpr ← expToBoole env bound none (unwrapViewCall arg)
        let fnIdx ← resolveFreeVar "Vec_len"
        return Bld.app (Bld.fvar fnIdx) vecExpr
      | _ => mkFallback
    else if isVecIndexSpecName fname || isVecIndexExecName fname then
      match argsFiltered with
      | [vArg, iArg] =>
        let vecExpr ← expToBoole env bound none (unwrapViewCall vArg)
        let rawIdx ← expToBoole env bound none iArg
        let idxExpr ← coerceNumeric (inferNumKind env bound iArg) (some (.bv usizeBitWidth false)) rawIdx
        let fnIdx ← resolveFreeVar "Vec_index"
        return Bld.appN (Bld.fvar fnIdx) [vecExpr, idxExpr]
      | _ => mkFallback
    else if fnameStr == "Seq_index" then
      match argsFiltered with
      | [sArg, iArg] =>
        mkSeqBuiltinCall "select"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (iArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_first" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let zero := intConst 0
        let selectIdx ← resolveFreeVar "Sequence.select"
        return Bld.appN (Bld.fvar selectIdx) [s, zero]
      | _ => mkFallback
    else if fnameStr == "Seq_last" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let one := intConst 1
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.select"))
          [s, intSub (seqLength s) one]
      | _ => mkFallback
    else if fnameStr == "Seq_empty" then do
      let fnIdx ← resolveFreeVar "Sequence.empty"
      return Bld.fvar fnIdx
    else if fnameStr == "Seq_update" then
      match argsFiltered with
      | [sArg, iArg, vArg] =>
        mkSeqBuiltinCall "update"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (iArg, some .Int),
           (vArg, lookupFnParamTypeFull env fnameStr 2)]
      | _ => mkFallback
    else if fnameStr == "Seq_push" then
      match argsFiltered with
      | [sArg, vArg] =>
        mkSeqBuiltinCall "build"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (vArg, lookupFnParamTypeFull env fnameStr 1)]
      | _ => mkFallback
    else if fnameStr == "Seq_take" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "take"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_skip" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "drop"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_add" then
      match argsFiltered with
      | [s1Arg, s2Arg] =>
        let seqTy? := lookupFnParamTypeFull env fnameStr 0
        mkSeqBuiltinCall "append" [(s1Arg, seqTy?), (s2Arg, seqTy?)]
      | _ => mkFallback
    else if fnameStr == "Seq_subrange" then
      match argsFiltered with
      | [sArg, startArg, endArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let start ← expToBoole env bound (some .Int) startArg
        let stop ← expToBoole env bound (some .Int) endArg
        let len := intSub stop start
        let dropped := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.drop")) [s, start]
        let taken := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [dropped, len]
        return taken
      | _ => mkFallback
    else if fnameStr == "Seq_lib_contains" then
      match argsFiltered with
      | [sArg, vArg] =>
        mkSeqBuiltinCall "contains"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (vArg, lookupFnParamTypeFull env fnameStr 1)]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_drop_last" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let one := intConst 1
        let lenMinusOne := intSub (seqLength s) one
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, lenMinusOne]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_remove" then
      match argsFiltered with
      | [sArg, iArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let i ← expToBoole env bound (some .Int) iArg
        let one := intConst 1
        let suffixStart := intAdd i one
        let prefixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, i]
        let suffixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.drop")) [s, suffixStart]
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.append")) [prefixSeq, suffixSeq]
      | _ => mkFallback
    else
      mkFallback
  | .CallLambda body args => do
    let fnExpr ← expToBoole env bound none body
    let args' ← args.mapM (expToBoole env bound none)
    return Bld.appN fnExpr args'
  | .Bind bind body =>
    match bind with
    | .Let v ty rhs =>
      let rhs' :=
        match rhs with
        | .ArrayLiteral elems =>
          if isSeqTyp ty then mkSeqLiteralExp elems else rhs
        | _ => rhs
      let body' := substExp v rhs' body
      expToBoole env bound expected? body'
    | .Quant q vars _trigs => do
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray
        expToBoole env (vars.reverse ++ bound) (some .Bool) body
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      match q with
      | .Forall => return forallExpr binds body'
      | .Exists => return existsExpr binds body'
    | .Lambda vars => do
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray
        expToBoole env (vars.reverse ++ bound) none body
      -- Lambda is represented as a quantifier for now; Boole does not yet get
      -- a source-faithful lambda node here.
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      return forallExpr binds body'
  | .MatchBlock _scrut body =>
    expToBoole env bound expected? body
  | .ArrayLiteral elems => do
    let elemExpected? :=
      if expected?.map isSeqTyp |>.getD false then
        firstStructParamFromExpected? expected?
      else
        none
    let args ← elems.mapM (expToBoole env bound elemExpected?)
    if expected?.map isSeqTyp |>.getD false then
      -- Lower `seq![a, b, c]` to Sequence.empty/Sequence.build chain
      let seqEmptyIdx ← resolveFreeVar "Sequence.empty"
      let seqBuildIdx ← resolveFreeVar "Sequence.build"
      return args.foldl (init := Bld.fvar seqEmptyIdx) (fun acc arg =>
        Bld.appN (Bld.fvar seqBuildIdx) [acc, arg])
    else do
      let litIdx ← resolveFreeVar s!"Array_literal_{elems.length}"
      return Bld.appN (Bld.fvar litIdx) args

private partial def extEqExpToBoole
    (env : VarEnv) (bound : BoundEnv)
    (_deep : Bool) (ty : Typ)
    (lhs rhs : Exp) : BuildM BExpr := do
  let lhs' ← expToBoole env bound (some ty) lhs
  let rhs' ← expToBoole env bound (some ty) rhs
  -- Simplified: use plain equality for all types
  -- Full version would do pointwise comparison for sequences/sets/maps
  return Bld.eqTyped (← typToBooleType ty) lhs' rhs'

end

abbrev expToBooleFlat (env : VarEnv) (expected? : Option Typ) (e : Exp) :
    BuildM BExpr :=
  expToBoole env [] expected? e

/-! ## Statement Translation -/

private def mkQueryObligation (env : VarEnv) (label : String) (requires ensures : List Exp) :
    BuildM (List BStmt) := do
  let reqs ← requires.mapM (expToBooleFlat env (some .Bool))
  let enss ← ensures.mapM (expToBooleFlat env (some .Bool))
  let ensConj := match enss with
    | [] => boolConst true
    | e :: rest => rest.foldl boolAnd e
  let reqs' := reqs.filter (fun e => match e with | .btrue _ => false | _ => true)
  let obligation :=
    if reqs'.isEmpty then ensConj
    else
      let reqConj := match reqs' with
        | [] => boolConst true
        | e :: rest => rest.foldl boolAnd e
      boolImplies reqConj ensConj
  return [assertStmt label obligation]

/-! ## Projected Assignment Support -/

private structure ProjLayout where
  dt : Ident
  variant : String
  ctorName : String
  fields : List String
  isEnum : Bool

private def projLayoutsFromDecl : Decl → List ProjLayout
  | .struct s =>
    [{ dt := s.name
       variant := datatypeNameOf s.name
       ctorName := structCtorNameOf s.name
       fields := s.fields.map Prod.fst
       isEnum := false }]
  | .enum e =>
    e.fields.map (fun field =>
      match field with
      | .labeled variant data =>
        { dt := e.name, variant := variant
          ctorName := enumCtorNameOf e.name variant
          fields := data.map (fun (fname, _) => projFieldNameOf e.name variant fname)
          isEnum := true }
      | .tuple variant ts =>
        { dt := e.name, variant := variant
          ctorName := enumCtorNameOf e.name variant
          fields := (List.range ts.length).map (fun i => projFieldNameOf e.name variant (toString i))
          isEnum := true })
  | .mutualBlock ds => ds.flatMap projLayoutsFromDecl
  | _ => []

private def buildProjLayouts (decls : List Decl) : List ProjLayout :=
  decls.flatMap projLayoutsFromDecl

private def findProjLayout? (layouts : List ProjLayout) (dt : Ident) (variant : String) :
    Option ProjLayout :=
  let dtName := datatypeNameOf dt
  let variantName := sanitizeIdent variant
  layouts.find? (fun l =>
    datatypeNameOf l.dt == dtName &&
      if l.isEnum then sanitizeIdent l.variant == variantName else true)

private def resolveProjFieldName? (layout : ProjLayout) (dt : Ident) (variant field : String) :
    Option String :=
  let candidates :=
    ([field, sanitizeIdent field,
      projFieldNameOf dt variant field,
      projFieldNameOf dt (datatypeNameOf dt) field]).eraseDups
  candidates.find? (fun c => layout.fields.contains c)

private def lvalueToExp : LValue → Exp
  | .Var name => .Var name
  | .Proj base dt variant field getVariant check =>
    .Unary (.Proj dt variant field getVariant check) (lvalueToExp base)
  | .Proj' base size field =>
    .Unary (.Proj' size field) (lvalueToExp base)

private def lvalueReadExprToBoole (env : VarEnv) (lv : LValue) : BuildM BExpr :=
  expToBooleFlat env none (lvalueToExp lv)

private partial def lowerProjectedAssignRhsToRoot
    (env : VarEnv) (projLayouts : List ProjLayout) :
    LValue → BExpr → BuildM (String × BExpr)
  | .Var name, rhs => pure (name, rhs)
  | .Proj base dt variant field _getVariant check, rhs => do
    if check == .Yes then
      throw s!"unsupported checked projection assignment: {dt}::{variant}.{field}"
    let container ← lvalueReadExprToBoole env base
    let some layout := findProjLayout? projLayouts dt variant
      | throw s!"missing projection layout for {dt}::{variant}.{field}"
    let some targetField := resolveProjFieldName? layout dt variant field
      | throw s!"could not resolve projection field `{field}` in `{dt}::{variant}`"
    if !layout.fields.contains targetField then
      throw s!"projection field `{targetField}` not found in datatype"
    let ctorIdx ← resolveFreeVar layout.ctorName
    let args ← layout.fields.mapM (fun fieldName => do
      if fieldName == targetField then
        pure rhs
      else do
        let projIdx ← resolveFreeVar (datatypeDestructorNameOf dt fieldName)
        pure (Bld.app (Bld.fvar projIdx) container))
    let updatedContainer := Bld.appN (Bld.fvar ctorIdx) args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer
  | .Proj' base size field, rhs => do
    let container ← lvalueReadExprToBoole env base
    if size == 2 then requireSupport .tuple
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let args ← (List.range size).mapM (fun i => do
      if i == field then pure rhs
      else do
        let projName :=
          if size == 2 then s!"Tuple.._{i}" else s!"Tuple_{size}_{i}"
        let projIdx ← resolveFreeVar projName
        pure (Bld.app (Bld.fvar projIdx) container))
    let updatedContainer := Bld.appN (Bld.fvar ctorIdx) args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer

/-! ## Statement Translation Main -/

mutual

partial def stmToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    Stm → BuildM (List BStmt)
  | .Call fn _typArgs args => do
    if isGhostPervasiveCallName fn then
      return []
    let argsFiltered := normalizeCallArgsForCallee env fn args
    let callee := identToBoole fn
    let argsBoole ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
      let paramTy? := lookupFnParamTypeFull env callee idx
      expToBooleFlat env paramTy? arg)
    -- Compute mutable outputs
    let infos := (mutArgMap.get? callee).getD []
    let mutOuts ← infos.filterMapM (fun info => do
      let i := info.idx
      match (argsFiltered.drop i).head? with
      | none => throw s!"mutable call-arg index {i} out of bounds for {callee}"
      | some arg =>
        match vecVarFromExp arg with
        | some v => pure (some (sanitizeVarName v))
        | none => pure none)
    return [callStmt (mutOuts.toArray) callee (argsBoole.toArray)]
  | .Assert exp | .AssertLean exp => do
    match exp with
    | .Unary (.HasType _) _ => return []
    | _ =>
      let e ← expToBooleFlat env (some .Bool) exp
      return [assertStmt "" e]
  | .AssertBitVector requires ensures =>
    mkQueryObligation env "bitvector_query" requires ensures
  | .AssertQuery mode body =>
    match queryReqEnsFromBody body with
    | some (reqs, enss) =>
      mkQueryObligation env (assertQueryModeLabel mode) reqs enss
    | none =>
      stmToBoole env projLayouts mutArgMap retVar? procName body
  | .AssertCompute exp => do
    let e ← expToBooleFlat env (some .Bool) exp
    return [assertStmt "compute" e]
  | .Assume exp => do
    let e ← expToBooleFlat env (some .Bool) exp
    return [assumeStmt "" e]
  | .Assign lhs lhsTy rhs _lhsIsInit => do
    if shouldDropAssignAsForLoopScaffolding lhs then
      return []
    match rhs with
    | .Call fn _typArgs args => do
      let fnName := CallFun.name fn
      if isGhostPervasiveCallName fnName then return []
      let argsFiltered := normalizeCallArgsForCallee env fnName args
      let callee := identToBoole fnName
      if (lookupFnRetTypeFull env callee).isSome then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else if isViewName fnName || isVecLenSpecName fnName || isVecLenExecName fnName
            || isVecIndexSpecName fnName || isVecIndexExecName fnName then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else
        let argsBoole ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
          let paramTy? := lookupFnParamTypeFull env callee idx
          expToBooleFlat env paramTy? arg)
        let infos := (mutArgMap.get? callee).getD []
        let mutOuts ← infos.filterMapM (fun info => do
          match (argsFiltered.drop info.idx).head? with
          | none => throw s!"mutable call-arg index {info.idx} out of bounds for {callee}"
          | some arg =>
            match vecVarFromExp arg with
            | some v => pure (some (sanitizeVarName v))
            | none => pure none)
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsNames := #[sanitizeVarName lhsName] ++ mutOuts.toArray
          return [callStmt lhsNames callee argsBoole.toArray]
        | none =>
          -- Projected l-value: use temporary
          let tmpName := sanitizeVarName s!"tmp_proj_call_{callee}"
          let ty' ← typToBooleType lhsTy
          let lhsNames := #[tmpName] ++ mutOuts.toArray
          let callS := callStmt lhsNames callee argsBoole.toArray
          let tmpExpr ← resolveVar tmpName
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs tmpExpr
          return [varStmt tmpName ty', callS, setStmt (sanitizeVarName rootName) updatedRoot]
    | _ => do
      let rhs' ← expToBooleFlat env (some lhsTy) rhs
      match lvalueVarName? lhs with
      | some lhsName =>
        let lhsTy' ← typToBooleType lhsTy
        return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
      | none =>
        let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
        return [setStmt (sanitizeVarName rootName) updatedRoot]
  | .DeadEnd stm =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | .Return exp => do
    match exp, retVar? with
    | some e, some (retName, retTy) =>
      match e with
      | .EnumCtor _ "tuple%0" [] | .TupleCtor 0 [] | .StructCtor _ [] =>
        return [returnStmt procName]
      | _ =>
        let rhs ← expToBooleFlat env (some retTy) e
        let retTy' ← typToBooleType retTy
        return [setStmtTyped retTy' (sanitizeVarName retName) rhs, returnStmt procName]
    | _, _ => return [returnStmt procName]
  | .BreakOrContinue label isBreak =>
    match label with
    | some l => return [exitStmt (some (sanitizeIdent l))]
    | none =>
      throw s!"unsupported unlabeled {(if isBreak then "break" else "continue")} after loop normalization"
  | .If cond b1 b2 => do
    let c ← expToBooleFlat env (some .Bool) cond
    let thenStms ← stmToBoole env projLayouts mutArgMap retVar? procName b1
    let elseStms ← match b2 with
      | some s => stmToBoole env projLayouts mutArgMap retVar? procName s
      | none => pure []
    return [iteStmt c thenStms.toArray elseStms.toArray]
  | .Loop _isForLoop label cond body invs decrease => do
    -- For-loop recovery is handled in stmListToBooleAux; if we get here, emit while loop
    let (guardFromBody?, body') :=
      match extractLoopGuardFromBody body with
      | some (g, b') => (some g, b')
      | none => (none, body)
    let loopLabel? ← do
      match label with
      | some l => pure (some (sanitizeIdent l))
      | none =>
        let condNeeds := match cond with | some (s, _) => hasUnlabeledLoopControl s | none => false
        if condNeeds || hasUnlabeledLoopControl body' then
          pure (some (← implicitLoopLabel))
        else
          pure none
    let condTempSubsts : List (String × Exp) :=
      match cond with
      | some (Stm.Block stms, _) => (splitAssignPrefix stms).fst
      | some (s, _) => match assignFromPrefix s with | some sub => [sub] | none => []
      | none => []
    let condExpr ←
      match cond with
      | some (_, e) => expToBooleFlat env (some .Bool) (substExps condTempSubsts e)
      | none =>
        match guardFromBody? with
        | some g => expToBooleFlat env (some .Bool) g
        | none => pure (boolConst true : BExpr)
    let invExprs ← invs.toArray.mapM (fun inv => expToBooleFlat env (some .Bool) inv.body)
    let measureExpr? ← match decrease with
      | [] => pure none
      | e :: _ => do
        let ce0 ← expToBooleFlat env none e
        let srcKind? := inferNumKind env [] e
        let ce ← coerceNumeric srcKind? (some .int) ce0
        pure (some ce)
    let bodyBound := match loopLabel? with | some l => bindUnlabeledLoopControlTo l body' | none => body'
    let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? procName bodyBound
    let loopStmt := whileStmt condExpr measureExpr? invExprs bodyStms.toArray
    let stmt := match loopLabel? with | some l => blockStmt l #[loopStmt] | none => loopStmt
    return [stmt]
  | .OpenInvariant stm =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | .ClosureInner body =>
    stmToBoole env projLayouts mutArgMap retVar? procName body
  | .Block stms =>
    stmListToBoole env projLayouts mutArgMap retVar? procName stms
  | .Reveal .. =>
    return []

/--
  Emit a recovered source-style `for` loop.  The VLIR shape matching and
  scaffolding filtering lives in `Boole.ForLoop`; this function only lowers the
  recovered loop plan to BooleDDM.
-/
partial def tryForLoopRecovery (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (retVar? : Option (String × Typ))
    (procName : String)
    (stms : List Stm) : BuildM (Option (List BStmt × List Stm)) := do
  match recoverForLoop? stms with
  | none => pure none
  | some loop => do
    let loopVarTy ← typToBooleType loop.loopVarTy
    let loopVarSan := sanitizeVarName loop.loopVarName
    let startExpr ← expToBooleFlat env (some loop.loopVarTy) loop.startExp
    let endE ← expToBooleFlat env (some loop.loopVarTy) loop.endExp
    let limitExpr ← match bitWidthOfTyp loop.loopVarTy with
      | some w => pure (bvSub w endE (bitvecConstNat w 1))
      | none => pure (intSub endE (intConst 1))
    let (invExprs, measureExpr?, bodyStms) ← withScope do
      pushBoundVar loopVarSan
      let invExprs ← loop.invariants.toArray.mapM (fun inv =>
        expToBooleFlat env (some .Bool) inv.body)
      let measureExpr? ← match loop.decrease with
        | [] => pure none
        | e :: _ => do
          let ce0 ← expToBooleFlat env none e
          let srcKind? := inferNumKind env [] e
          let ce ← coerceNumeric srcKind? (some .int) ce0
          pure (some ce)
      let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? procName (Stm.Block loop.userBody)
      pure (invExprs, measureExpr?, bodyStms)
    let loopStmt := forToStmt loopVarSan loopVarTy startExpr limitExpr
      measureExpr? invExprs bodyStms.toArray
    let preBoole ← loop.preStms.mapM (stmToBoole env projLayouts mutArgMap retVar? procName)
    pure (some (preBoole.flatten ++ [loopStmt], loop.postStms))

partial def stmListToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    List Stm → BuildM (List BStmt)
  | stms => do
    let normalized :=
      (flattenSeqBlocks (recoverComputeProofs (inlineTemps isPureBooleBuiltinCallName stms))).map stripSingletonBlocks
    -- Try for-loop recovery before normal processing
    let hasForLoop := normalized.any fun
      | .Loop true _ _ _ _ _ => true
      | _ => false
    if hasForLoop then
      match ← tryForLoopRecovery env projLayouts mutArgMap retVar? procName normalized with
      | some (forStms, postStms) =>
        let rest ← stmListToBooleAux env projLayouts mutArgMap retVar? procName postStms
        return forStms ++ rest
      | none =>
        stmListToBooleAux env projLayouts mutArgMap retVar? procName normalized
    else
      stmListToBooleAux env projLayouts mutArgMap retVar? procName normalized

partial def stmListToBooleAux (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    List Stm → BuildM (List BStmt)
  | (.BreakOrContinue none true) :: (.Assume (.Const (.Bool false) _)) :: rest => do
    let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName rest
    return [assumeStmt "" (boolConst false)] ++ s2
  | a :: (.Assume e) :: next :: rest =>
    if isAssertAssumeEcho a e then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (a :: next :: rest)
    else if isTrivialTrueAssert a && isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
    else if isTrivialTrueAssert a then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.AssertCompute e) :: next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.Assume e) :: next :: rest)
      return s1 ++ s2
  | (.Assume e) :: next :: rest =>
    if isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName (.Assume e)
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
      return s1 ++ s2
  | a :: next :: rest =>
    match next with
    | .Assume e =>
      if isAssertAssumeEcho a e then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName (a :: rest)
      else if isTrivialTrueAssert a then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.AssertCompute e) :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
        return s1 ++ s2
    | _ =>
      if isTrivialTrueAssert a && isQueryStmt next then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
        return s1 ++ s2
  | [stm] =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | [] => return []
end

/-! ## Declaration Translation -/

def typeArgsFromTyps (tys : List Typ) : List String :=
  (tys.flatMap typTypeVars).eraseDups

def typeArgsFromDecls (decls : List (String × Typ)) : List String :=
  typeArgsFromTyps (decls.map Prod.snd)

private def localDecl (name : String) (ty : Typ) (origin : LocalDeclOrigin) : LocalDeclInfo :=
  { name := name, ty := ty, origin := origin }

private def localBindings (locals : List LocalDeclInfo) : List (String × Typ) :=
  locals.map LocalDeclInfo.toPair

def dedupLocals (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  let rec go (seen : Std.HashSet String) (acc : List LocalDeclInfo) : List LocalDeclInfo → List LocalDeclInfo
    | [] => acc.reverse
    | decl :: rest =>
      if seen.contains decl.name then go seen acc rest
      else go (seen.insert decl.name) (decl :: acc) rest
  go ∅ [] locals

partial def collectSetVars : Stm → List LocalDeclInfo
  | .Assign lhs lhsTy _rhs lhsIsInit =>
    if lhsIsInit then []
    else match lvalueVarName? lhs with
      | some name => [localDecl name lhsTy .implicitSet]
      | none => []
  | .AssertQuery _ body => collectSetVars body
  | .DeadEnd stm => collectSetVars stm
  | .If _cond b1 b2 =>
    collectSetVars b1 ++ (b2.map collectSetVars).getD []
  | .Loop _isForLoop _label cond body _invs _decrease =>
    let condVars := match cond with | some (s, _) => collectSetVars s | none => []
    condVars ++ collectSetVars body
  | .OpenInvariant stm => collectSetVars stm
  | .ClosureInner body => collectSetVars body
  | .Block stms => stms.flatMap collectSetVars
  | _ => []

private def localShouldEmit (hasForLoop : Bool) (decl : LocalDeclInfo) : Bool :=
  !decl.isSourceDecreases &&
    !shouldDropForLoopScaffoldingLocal decl.name &&
    !(hasForLoop && isForLoopScaffoldingVar decl.name) &&
    !isUnitLikeTyp decl.ty

private partial def stmHasForLoop : Stm → Bool
  | .Loop true _ _ _ _ _ => true
  | .Block stms => stms.any stmHasForLoop
  | .If _ b1 b2 => stmHasForLoop b1 || (b2.map stmHasForLoop).getD false
  | .DeadEnd stm => stmHasForLoop stm
  | _ => false

private def collectProcedureLocals
    (sourceLocals : List LocalDeclInfo)
    (inputNames retNames : List String)
    (setVars : List LocalDeclInfo)
    (hasForLoop : Bool := false) : List LocalDeclInfo :=
  let declaredInInputsRetOrLocals := fun (n : String) =>
    inputNames.any (fun x => x == n) ||
    retNames.any (fun x => x == n) ||
    sourceLocals.any (fun decl => decl.name == n)
  let implicitSetLocals := dedupLocals <| setVars.filter (fun decl =>
    !declaredInInputsRetOrLocals decl.name)
  let localsAll := dedupLocals <|
    (sourceLocals.filter (fun decl =>
      !(inputNames.any (fun x => x == decl.name) || retNames.any (fun x => x == decl.name))) ++
      implicitSetLocals)
  localsAll.filter (localShouldEmit hasForLoop)

/-- Apply the same `inlineTemps` pass the statement-list translator runs
    (see `stmListToBoole`), so body analyses that happen *before* translation
    (local-liveness, set-var collection) see the post-inlined shape rather
    than the raw VLIR shape that still has one-shot `tmp := rhs` prefixes. -/
private def normalizeForLocalFilter (body : Stm) : Stm :=
  match body with
  | .Block stms => .Block (inlineTemps isPureBooleBuiltinCallName stms)
  | s => inlineTempsInStm isPureBooleBuiltinCallName s

/-- Collect names of tmp vars that will be hoisted out by
    `extractLoopGuardFromBody` during Loop translation. Such tmps disappear
    from the emitted Boole body (their assignments are elided and their
    references are substituted into the hoisted guard expression), so their
    `var tmp : T;` declarations would otherwise be orphaned. Mirrors the
    predicate in `stmToBoole`'s `.Loop` handler. -/
private partial def collectHoistedGuardTmps : Stm → List String
  | .Loop _ _ _ body _ _ =>
    let hereTmps := match body with
      | .Block stms =>
        -- Mirror `extractLoopGuardFromBody`: flatten nested blocks and
        -- strip singletons before scanning the prefix. Without this, a
        -- body shaped `Block [Block [tmp_assign ...]]` (common in VLIR)
        -- wouldn't expose its tmp prefix.
        let linear := (flattenSeqBlocks stms).map stripSingletonBlocks
        (splitGuardTempPrefix linear).fst.map Prod.fst
      | _ => []
    hereTmps ++
      (match body with
       | .Block stms => stms.flatMap collectHoistedGuardTmps
       | b => collectHoistedGuardTmps b)
  | .Block stms => stms.flatMap collectHoistedGuardTmps
  | .If _ b1 b2 =>
    collectHoistedGuardTmps b1 ++ (b2.map collectHoistedGuardTmps).getD []
  | .AssertQuery _ body | .DeadEnd body | .OpenInvariant body | .ClosureInner body =>
    collectHoistedGuardTmps body
  | _ => []

/-- Drop procedure locals that are unreferenced by the (post-inline) body:
    Verus declares VLIR locals unconditionally, but our `inlineTemps` pass
    (and `extractLoopGuardFromBody` for Loop prefixes) can eliminate every
    use of a tmp, leaving the `var tmp : T;` declaration as dead output
    clutter. -/
private def filterLocalsByUse
    (body : Stm) (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  -- Exclude tmps the Loop-guard extractor will hoist out: mentioning them
  -- in the VLIR body doesn't mean they'll appear in the emitted Boole.
  let hoisted := collectHoistedGuardTmps body
  locals.filter (fun decl =>
    !(hoisted.contains decl.name) && stmMentionsVar decl.name body)

/-! ### Building BooleDDM Commands -/

private def mkMonoInputs (inputs : List (String × Typ)) :
    BuildM (BooleDDM.Bindings SourceRange × Array String) := do
  let mut bindings : Array (BooleDDM.Binding SourceRange) := #[]
  let mut names : Array String := #[]
  for (name, ty) in inputs do
    let sanName := sanitizeVarName name
    let ty' ← typToBooleType ty
    bindings := bindings.push
      (BooleDDM.Binding.mkBinding default (ann sanName) (BooleDDM.TypeP.expr ty'))
    names := names.push sanName
  pure (BooleDDM.Bindings.mkBindings default (ann bindings), names)

private def mkMonoOutputs (outputs : List (String × Typ)) :
    BuildM (Option (BooleDDM.MonoDeclList SourceRange) × Array String) := do
  if outputs.isEmpty then
    pure (none, #[])
  else
    let first := outputs.head!
    let firstName := sanitizeVarName first.1
    let firstTy ← typToBooleType first.2
    let init := MonoDeclList.monoDeclAtom default
      (MonoBind.mono_bind_mk default (ann firstName) firstTy)
    let (result, names) ← outputs.tail.foldlM (fun (acc, names) (name, ty) => do
      let sanName := sanitizeVarName name
      let ty' ← typToBooleType ty
      pure (MonoDeclList.monoDeclPush default acc
        (MonoBind.mono_bind_mk default (ann sanName) ty'),
        names.push sanName))
      (init, #[firstName])
    pure (some result, names)

private def mkSpecElts (env : VarEnv) (pre post : List Exp) (modifies : List String) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  for e in pre do
    let e' ← expToBooleFlat env (some .Bool) e
    elts := elts.push (.requires_spec default noLabel (ann none) e')
  for e in post do
    let e' ← expToBooleFlat env (some .Bool) e
    elts := elts.push (.ensures_spec default noLabel (ann none) e')
  if !modifies.isEmpty then
    let modNames := modifies.toArray.map (fun n => ann (sanitizeVarName n))
    elts := elts.push (.modifies_spec default (ann modNames))
  pure elts

private def localsToVarStmts (locals : List LocalDeclInfo) : BuildM (List BStmt) := do
  locals.mapM (fun decl => do
    let ty' ← typToBooleType decl.ty
    let sanName := sanitizeVarName decl.name
    pushBoundVar sanName
    pure (varStmt sanName ty'))

/-! ### Spec Function Translation -/

private partial def collectSpecFns : List Decl → SpecFnMap
  | [] => ∅
  | d :: rest =>
    let here :=
      match d with
      | Decl.specFn f => [(f.name, f)]
      | Decl.mutualBlock ds =>
        ds.filterMap (fun d => match d with | Decl.specFn f => some (f.name, f) | _ => none)
      | _ => []
    let m := collectSpecFns rest
    here.foldl (init := m) (fun acc (k, v) => acc.insert k v)

private def addFnRetTypes (env : VarEnv) (sfMap : SpecFnMap) : VarEnv :=
  sfMap.fold (init := env) (fun acc name sf =>
    let fnStr := identToBoole name
    let acc := acc.insert (fnRetKey fnStr) sf.returnType
    sf.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
      acc.insert (fnParamKey fnStr idx) ty))

private partial def addAllFnParamTypes (env : VarEnv) (decls : List Decl) : VarEnv :=
  decls.foldl (init := env) (fun acc d =>
    match d with
    | .proofFn f =>
      let fnStr := identToBoole f.name
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .execFn f =>
      let fnStr := identToBoole f.name
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .mutualBlock ds => addAllFnParamTypes acc ds
    | _ => acc)

private partial def addDatatypeAccessorRetTypes (env : VarEnv) (decls : List Decl) : VarEnv :=
  decls.foldl (init := env) (fun acc d =>
    match d with
    | .struct s =>
      s.fields.foldl (init := acc) (fun acc (field, ty) =>
        let projField := projFieldNameOf s.name (datatypeNameOf s.name) field
        acc.insert (fnRetKey (datatypeDestructorNameOf s.name projField)) ty)
    | .enum e =>
      e.fields.foldl (init := acc) (fun acc field =>
        match field with
        | .labeled variant fields =>
          fields.foldl (init := acc) (fun acc (field, ty) =>
            let projField := projFieldNameOf e.name variant field
            acc.insert (fnRetKey (datatypeDestructorNameOf e.name projField)) ty)
        | .tuple variant tys =>
          tys.zipIdx.foldl (init := acc) (fun acc (ty, idx) =>
            let projField := projFieldNameOf e.name variant (toString idx)
            acc.insert (fnRetKey (datatypeDestructorNameOf e.name projField)) ty))
    | .mutualBlock ds => addDatatypeAccessorRetTypes acc ds
    | _ => acc)

private partial def collectNoParamFnNamesFromDecls : List Decl → List String
  | [] => []
  | d :: rest =>
    let here :=
      match d with
      | .specFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .proofFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .execFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .func f => if f.decls.isEmpty then [identToBoole f.name] else []
      | .mutualBlock ds => collectNoParamFnNamesFromDecls ds
      | _ => []
    (here ++ collectNoParamFnNamesFromDecls rest).eraseDups

private partial def collectMutArgMapFromDecls (decls : List Decl) : MutArgMap :=
  let rec go (acc : MutArgMap) : List Decl → MutArgMap
    | [] => acc
    | d :: rest =>
      let acc' :=
        match d with
        | .execFn f =>
          let infos := mutArgInfos f.inputs
          if infos.isEmpty then acc else acc.insert (identToBoole f.name) infos
        | .mutualBlock ds => go acc ds
        | _ => acc
      go acc' rest
  go (∅ : MutArgMap) decls

/-! ### SpecFn → BCmd -/

/-- Peel `Box`/`Unbox`/`Decorated` wrappers to find an underlying `.Var` name,
    if any. Used to decide whether a `.Proj` is being applied directly to a
    named parameter (and thus needs a caller-supplied variant precondition). -/
private partial def unwrapToVar : Exp → Option String
  | .Var x => some x
  | .Unary (.Box _) e | .Unary (.Unbox _) e => unwrapToVar e
  | _ => none

/-- Collect `(paramName, dt, variant)` triples for every `.Proj` appearing on
    the *root* path of the body — i.e. not under any control-flow node
    (`.If`/`.Bind`/`.MatchBlock`/etc.) which would already constrain the
    variant via a surrounding guard.

    Used by spec-fn translation to synthesise `requires <dt>..is<variant>(x)`
    preconditions for Verus's inline accessor sugar (`self->Variant.field`),
    which Verus encodes as `.Unary (.Proj dt variant field _ check:None)`
    without recording the partiality on the function. Without this, Strata
    correctly flags the implicit variant precondition of the datatype
    destructor as an unprovable obligation inside every such function body. -/
private partial def rootExposedProjs : Exp → List (String × Ident × String)
  | .Unary (.Proj dt variant _ _ _) arg =>
    let here := match unwrapToVar arg with
      | some name => [(name, dt, variant)]
      | none => []
    here ++ rootExposedProjs arg
  | .Unary _ arg => rootExposedProjs arg
  | .Binary _ a b => rootExposedProjs a ++ rootExposedProjs b
  | _ => []

private def dedupVariantReqs (xs : List (String × Ident × String)) :
    List (String × Ident × String) :=
  xs.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

/-- Build `requires <dt>..is<variant>(<param>)` SpecElts from `rootExposedProjs`
    output. Assumes the function's input names have already been `addBoundVars`-ed
    in the current scope so the tester argument resolves to a bvar.

    Skips Projs on struct-typed parameters (single-variant datatypes): Strata
    generates no tester for those, and the precondition would be trivially
    true anyway. We detect this by looking up the tester name in the current
    free-variable registry — only multi-variant enum translation
    (`enumToBoole`) registers tester names. -/
private def synthVariantRequires
    (reqs : List (String × Ident × String)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  for (paramName, dt, variant) in reqs do
    let testerName := enumTesterNameOf dt variant
    let ctx ← get
    match ctx.freeVarIndex? testerName with
    | none =>
      -- Tester not registered: the datatype is a struct (one variant) or
      -- this Proj targets a name Strata doesn't recognise. Either way the
      -- precondition is trivial; skip.
      continue
    | some testerIdx =>
      let paramExpr ← resolveVar paramName
      let cond := Bld.app (Bld.fvar testerIdx) paramExpr
      elts := elts.push (.requires_spec default noLabel (ann none) cond)
  pure elts

def specFnToBoole (env : VarEnv) (emitBody : Bool) (f : SpecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let (inputBindings, inputNames) ← mkMonoInputs f.inputs
  let outputTy ← typToBooleType f.returnType
  let envLocal := extendEnv env f.inputs
  let (body?, specElts) ← withScope do
    addBoundVars inputNames
    let body? ← if emitBody then
      match f.body with
      | some b => pure (some (← expToBooleFlat envLocal (some f.returnType) b))
      | none => pure none
    else pure none
    -- Synthesise variant-precondition `requires` for Verus's inline accessor
    -- pattern (`impl&%N::arrow_*` style spec fns whose body is a bare
    -- `.Proj`). See `rootExposedProjs` for the detection rule.
    let inputNameSet := inputNames.toList
    let variantReqs := match f.body with
      | some b =>
        dedupVariantReqs <| (rootExposedProjs b).filter (fun (n, _, _) => inputNameSet.contains n)
      | none => []
    let elts ← synthVariantRequires variantReqs
    pure (body?, elts)
  match body? with
  | some body =>
    if f.isRecursive then
      let recDecl :=
        BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy (ann specElts) body
      pure (.command_recfndefs default (ann #[recDecl]))
    else
      pure (.command_fndef default name typeArgs inputBindings outputTy (ann specElts) body (ann none))
  | none =>
    pure (.command_fndecl default name typeArgs inputBindings outputTy)

/-! ### ProofFn/ExecFn → BCmd -/

def proofFnToBoole (env : VarEnv) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ProofFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let hasRet := match f.returnType with | .Unit | .Empty => false | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let retNames := if hasRet then [f.retName] else []
  let bodyStm? := f.body.map (fun b =>
    let b := expandReveals sfMap b
    let b := stripDecreaseArtifacts b
    let b := normalizeForLocalFilter b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s)
  let setVars := match bodyStm? with | some body => collectSetVars body | none => []
  let bodyHasForLoop := match bodyStm? with | some body => stmHasForLoop body | none => false
  let inputNames := f.inputs.map Prod.fst
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let localsAll := match bodyStm? with
    | some body => filterLocalsByUse body localsAll
    | none => localsAll
  let outputs := retDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.requires f.ensures []
    let localStmts ← localsToVarStmts localsAll
    let retVar? := if hasRet then some (f.retName, f.returnType) else none
    let bodyStmts ← match bodyStm? with
      | some stm => stmToBoole envLocal projLayouts mutArgMap retVar? fnName stm
      | none => pure []
    let allStmts := localStmts ++ bodyStmts
    let body := BooleDDM.Block.block default (ann allStmts.toArray)
    pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.command_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

def execFnToBoole (env : VarEnv) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ExecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let mutOutDecls :=
    f.inputs.filterMap (fun (n, t) =>
      (mutRefPayload? t).map (fun payloadTy => (n, s!"{n}_out", payloadTy)))
  let mutRenames := mutOutDecls.map (fun (n, outName, _) => (n, outName))
  let rewrittenBody :=
    let b := stripDecreaseArtifacts (expandReveals sfMap (applyNameSubstsStm mutRenames f.body))
    let b := normalizeForLocalFilter b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s
  let rewrittenEnsures := f.ensures.map (applyNameSubstsExp mutRenames)
  let hasRet := match f.returnType with | .Unit | .Empty => false | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let mutOutputDecls := mutOutDecls.map (fun (_, outName, payloadTy) => (outName, payloadTy))
  let inputNames := f.inputs.map Prod.fst
  let retNames := (if hasRet then [f.retName] else []) ++ mutOutputDecls.map Prod.fst
  let setVars := collectSetVars rewrittenBody
  let bodyHasForLoop := stmHasForLoop rewrittenBody
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let localsAll := filterLocalsByUse rewrittenBody localsAll
  let outputs := retDecls ++ mutOutputDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let isDeclOnly := match f.body with | .Block [] => true | _ => false
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.requires rewrittenEnsures []
    if isDeclOnly then
      let body := BooleDDM.Block.block default (ann #[])
      pure (specElts, body)
    else
      let localStmts ← localsToVarStmts localsAll
      -- Init mutable-out variables from inputs
      let mutOutInits ← mutOutDecls.mapM (fun (inName, outName, payloadTy) => do
        let inExpr ← resolveVar inName
        let outTy ← typToBooleType payloadTy
        pure (setStmtTyped outTy (sanitizeVarName outName) inExpr))
      let retVar? := if hasRet then some (f.retName, f.returnType) else none
      let bodyStmts ← stmToBoole envLocal projLayouts mutArgMap retVar? fnName rewrittenBody
      let allStmts := localStmts ++ mutOutInits ++ bodyStmts
      let body := BooleDDM.Block.block default (ann allStmts.toArray)
      pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.command_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

/-! ### Struct/Enum → BCmd -/

def structToBoole (s : Struct) : BuildM BCmd := do
  let dtName := datatypeNameOf s.name
  addFreeVars #[dtName]
  let ctorName := structCtorNameOf s.name
  let testerName := s!"{dtName}..is{ctorName}"
  let fieldNames := s.fields.map (fun (f, _) => fieldAccessorNameOf f)
  addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
  let constrArgs ← if s.fields.isEmpty then
    pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
  else do
    let bindings ← s.fields.toArray.mapM fun (fname, ty) => do
      let ty' ← typToBooleType ty
      pure (BooleDDM.Binding.mkBinding default (ann (fieldAccessorNameOf fname)) (BooleDDM.TypeP.expr ty'))
    pure (ann (some (ann bindings)))
  let constr := BooleDDM.Constructor.constructor_mk default (ann ctorName) constrArgs
  let constrList := BooleDDM.ConstructorList.constructorListAtom default constr
  let typeArgs : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    if s.typeParams.isEmpty then ann none
    else
      let bindings := s.typeParams.toArray.map fun param =>
        BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
      ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
  let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann dtName) typeArgs constrList
  pure (.command_datatypes default (ann #[dtDecl]))

def enumToBoole (e : Enum) : BuildM BCmd := do
  let dtName := datatypeNameOf e.name
  addFreeVars #[dtName]
  if e.fields.isEmpty then
    -- Abstract type
    let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if e.typeParams.isEmpty then ann none
      else
        let bindings := e.typeParams.toArray.map fun param =>
          BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    pure (.command_typedecl default (ann dtName) args)
  else
    -- Register all names
    for field in e.fields do
      match field with
      | .labeled variant data =>
        let ctorName := enumCtorNameOf e.name variant
        let testerName := enumTesterNameOf e.name variant
        let fieldNames := data.map (fun (fname, _) => projFieldNameOf e.name variant fname)
        addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
      | .tuple variant ts =>
        let ctorName := enumCtorNameOf e.name variant
        let testerName := enumTesterNameOf e.name variant
        let fieldNames := (List.range ts.length).map (fun i => projFieldNameOf e.name variant (toString i))
        addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
    let constrs ← e.fields.toArray.mapM fun field => do
      match field with
      | .labeled variant data =>
        let constrArgs ← if data.isEmpty then
          pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
        else do
          let bindings ← data.toArray.mapM fun (fname, ty) => do
            let ty' ← typToBooleType ty
            let fieldName := projFieldNameOf e.name variant fname
            pure (BooleDDM.Binding.mkBinding default (ann fieldName) (BooleDDM.TypeP.expr ty'))
          pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann (enumCtorNameOf e.name variant)) constrArgs)
      | .tuple variant ts =>
        let constrArgs ← if ts.isEmpty then
          pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
        else do
          let bindings ← ts.zipIdx.toArray.mapM fun (ty, i) => do
            let ty' ← typToBooleType ty
            let fieldName := projFieldNameOf e.name variant (toString i)
            pure (BooleDDM.Binding.mkBinding default (ann fieldName) (BooleDDM.TypeP.expr ty'))
          pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann (enumCtorNameOf e.name variant)) constrArgs)
    let constrList :=
      if constrs.isEmpty then
        BooleDDM.ConstructorList.constructorListAtom default
          (BooleDDM.Constructor.constructor_mk default (ann "") (ann none))
      else
        constrs[1:].foldl
          (fun acc c => BooleDDM.ConstructorList.constructorListPush default acc c)
          (BooleDDM.ConstructorList.constructorListAtom default constrs[0]!)
    let typeArgs : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if e.typeParams.isEmpty then ann none
      else
        let bindings := e.typeParams.toArray.map fun param =>
          BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann dtName) typeArgs constrList
    pure (.command_datatypes default (ann #[dtDecl]))

/-! ### FuncCheckSst → BCmd -/

def funcCheckSstToBoole (env : VarEnv) (f : FuncCheckSst) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.decls .Unit)
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.decls
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs []
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env f.decls
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.reqs f.postCondition []
    let body := BooleDDM.Block.block default (ann #[])
    pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.command_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

/-! ### Top-Level Declaration Translation -/

partial def declToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (sfMap : SpecFnMap)
    (allDecls : List Decl) :
    Decl → BuildM (List BCmd)
  | .assertion _ => return []
  | .specFn f => do
    let cmd ← specFnToBoole env (!f.isOpaque) f
    return [cmd]
  | .proofFn f => do
    let cmd ← proofFnToBoole env projLayouts mutArgMap sfMap f
    return [cmd]
  | .execFn f => do
    let cmd ← execFnToBoole env projLayouts mutArgMap sfMap f
    return [cmd]
  | .func f => do
    let cmd ← funcCheckSstToBoole env f
    return [cmd]
  | .struct s => do
    let cmd ← structToBoole s
    return [cmd]
  | .enum e => do
    let cmd ← enumToBoole e
    return [cmd]
  | .mutualBlock ds => do
    -- Separate spec functions from other declarations
    let specFns := ds.filterMap (fun d => match d with | .specFn f => some f | _ => none)
    let others := ds.filter (fun d => match d with | .specFn _ => false | _ => true)
    -- Translate spec functions as a recursive block
    let recCmds ← if specFns.isEmpty then pure []
    else do
      for f in specFns do addFreeVars #[identToBoole f.name]
      let recDecls ← specFns.toArray.mapM fun f => do
        let fnName := identToBoole f.name
        let name := ann fnName
        let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
        let (inputBindings, inputNames) ← mkMonoInputs f.inputs
        let outputTy ← typToBooleType f.returnType
        let envLocal := extendEnv env f.inputs
        let (body, specElts) ← withScope do
          addBoundVars inputNames
          let body ← match f.body with
            | some b => expToBooleFlat envLocal (some f.returnType) b
            | none => pure (boolConst true)
          -- Same variant-precondition synthesis as the non-mutual path.
          let inputNameSet := inputNames.toList
          let variantReqs := match f.body with
            | some b =>
              dedupVariantReqs <|
                (rootExposedProjs b).filter (fun (n, _, _) => inputNameSet.contains n)
            | none => []
          let elts ← synthVariantRequires variantReqs
          pure (body, elts)
        pure (BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy (ann specElts) body)
      pure [BooleDDM.Command.command_recfndefs default (ann recDecls)]
    -- Translate non-spec declarations normally
    let otherCmds ← others.foldlM (fun acc d => do
      let cmds ← declToBoole env projLayouts mutArgMap sfMap allDecls d
      return acc ++ cmds) []
    return recCmds ++ otherCmds

/-! ## Prelude and Entry Point -/

private def buildEnv (decls : List Decl)
    (noParamFns : List String) (sfMap : SpecFnMap) : VarEnv :=
  let inputDecls := decls.flatMap (fun d => match d with
    | .specFn f => f.inputs
    | .proofFn f => f.inputs ++ [(f.retName, f.returnType)] ++ localBindings f.locals
    | .execFn f => f.inputs ++ [(f.retName, f.returnType)] ++ localBindings f.locals
    | .func f => f.decls
    | .struct s => s.fields
    | .enum e => e.fields.flatMap (fun field => match field with
        | .labeled _ data => data
        | .tuple _ ts => ts.zipIdx.map (fun (ty, i) => (s!"_{i}", ty)))
    | _ => [])
  let env := addNoParamFnMarkers (envFromDecls inputDecls) noParamFns
  let env := addFnRetTypes env sfMap
  let env := addAllFnParamTypes env decls
  let env := addDatatypeAccessorRetTypes env decls
  env

/-- Extract the primary name from a VLIR declaration. -/
private def declPrimaryName : Decl → String
  | .assertion a => a.name.toString
  | .specFn f => f.name.toString
  | .proofFn f => f.name.toString
  | .execFn f => f.name.toString
  | .struct s => s.name.toString
  | .enum e => e.name.toString
  | .func f => f.name.toString
  | .mutualBlock ds => match ds with | d :: _ => declPrimaryName d | [] => ""

/-- Check whether a VLIR declaration is purely for-loop iterator scaffolding
    that should be pruned when for-loops are successfully recovered. -/
private def isForLoopScaffoldingDecl (name : String) : Bool :=
  let lower := name.toLower
  -- Iterator next/into_iter procedures
  lower.endsWith "next" && lower.contains "iterator" ||
  lower.endsWith "into_iter" && lower.contains "collect" ||
  -- Ghost pervasive functions (ForLoopGhostIterator, ForLoopGhostIteratorNew)
  lower.contains "pervasive" && (lower.contains "ghost" || lower.contains "forloop") ||
  -- Range datatype (core.ops.range.Range or Ops_Range_range)
  (lower.contains "range" && (lower.contains "ops" || lower.contains "ops_range")) ||
  -- Option datatype (core.option.Option or Option_option)
  (lower.contains "option" && (lower.contains "core" || lower.contains "option_option")) ||
  -- Std specs for iterators (std_specs.range, std_specs.core.iter)
  lower.contains "std_specs" && (lower.contains "iter" || lower.contains "range") ||
  -- RangeGhostIterator
  lower.contains "rangeghost"

/-- Check whether any ExecFn in a declaration list has a for-loop body. -/
private def declsHaveForLoop (decls : List Decl) : Bool :=
  decls.any fun
    | .execFn f => stmHasForLoop f.body
    | .proofFn f => f.body.map stmHasForLoop |>.getD false
    | _ => false

/-! ### Dead-accessor pruning

Verus synthesises one `->`-accessor spec fn per field per variant (a.k.a.
`impl&%N::arrow_*`), eagerly for every enum in scope. Most of these go
unused in any given test, but we translate them all — producing long
stretches of never-called `Impl__N_arrow_*` decls that bloat the
emitted Boole source and slow Strata's verification pass.

The pruning pass below keeps an impl-accessor only if it's transitively
referenced from a non-impl decl. Modelled after the boogie branch's
`pruneUnreferencedSyntheticHelpers` but operating on VLIR `Decl`s
rather than Core ones. -/

/-- Identify the name prefix Verus uses for auto-generated impl-block
    accessor spec fns. Matches after `identToBoole` sanitisation, which
    preserves `Impl__N_` / `impl__N_` segments. -/
private def isSyntheticImplName (s : String) : Bool :=
  s.startsWith "Impl__" || s.startsWith "impl__"

private def declIsSyntheticImpl : Decl → Bool
  | .specFn f => isSyntheticImplName (identToBoole f.name)
  | _ => false

private def declName? : Decl → Option String
  | .specFn f => some (identToBoole f.name)
  | .proofFn f => some (identToBoole f.name)
  | .execFn f => some (identToBoole f.name)
  | .func f => some (identToBoole f.name)
  | .struct _ | .enum _ | .assertion _ | .mutualBlock _ => none

private partial def expCallRefs : Exp → List String
  | .Call fn _ args =>
    let here := identToBoole (CallFun.name fn)
    let rest := args.flatMap expCallRefs
    here :: rest
  | .CallLambda body args =>
    expCallRefs body ++ args.flatMap expCallRefs
  | .StructCtor _ fields => fields.flatMap (fun (_, e) => expCallRefs e)
  | .EnumCtor _ _ fields => fields.flatMap (fun (_, e) => expCallRefs e)
  | .TupleCtor _ data => data.flatMap expCallRefs
  | .Unary _ e => expCallRefs e
  | .Binary _ a b => expCallRefs a ++ expCallRefs b
  | .If c t f => expCallRefs c ++ expCallRefs t ++ expCallRefs f
  | .Bind bind body =>
    let bindRefs := match bind with
      | .Let _ _ rhs => expCallRefs rhs
      | .Quant _ _ trigs => trigs.flatMap (fun g => g.flatMap expCallRefs)
      | .Lambda _ => []
    bindRefs ++ expCallRefs body
  | .ArrayLiteral elems => elems.flatMap expCallRefs
  | .MatchBlock (scrut, _) body => expCallRefs scrut ++ expCallRefs body
  | .Const _ _ | .Var _ => []

private partial def stmCallRefs : Stm → List String
  | .Call fn _ args => identToBoole fn :: args.flatMap expCallRefs
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expCallRefs e
  | .AssertBitVector reqs enss =>
    reqs.flatMap expCallRefs ++ enss.flatMap expCallRefs
  | .AssertQuery _ body => stmCallRefs body
  | .Assign _ _ e _ => expCallRefs e
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => stmCallRefs s
  | .Return e? => (e?.map expCallRefs).getD []
  | .BreakOrContinue _ _ | .Reveal .. => []
  | .If cond b1 b2 =>
    expCallRefs cond ++ stmCallRefs b1 ++ (b2.map stmCallRefs).getD []
  | .Loop _ _ cond body invs decrease =>
    let condRefs := match cond with
      | some (s, e) => stmCallRefs s ++ expCallRefs e
      | none => []
    condRefs ++ stmCallRefs body ++ invs.flatMap (fun inv => expCallRefs inv.body) ++
      decrease.flatMap expCallRefs
  | .Block stms => stms.flatMap stmCallRefs

private partial def declRefs : Decl → List String
  | .assertion _ => []
  | .specFn f => (f.body.map expCallRefs).getD []
  | .proofFn f =>
    f.requires.flatMap expCallRefs ++ f.ensures.flatMap expCallRefs ++
      (f.body.map stmCallRefs).getD []
  | .execFn f =>
    f.requires.flatMap expCallRefs ++ f.ensures.flatMap expCallRefs ++
      stmCallRefs f.body
  | .func f =>
    f.reqs.flatMap expCallRefs ++ f.postCondition.flatMap expCallRefs
  | .struct _ | .enum _ => []
  | .mutualBlock ds => ds.flatMap declRefs

/-- Fixed-point closure: starting from `seed` impl-names, repeatedly add
    impl-names referenced by kept impl decls until the frontier stabilises. -/
private partial def closeImplRefs (implDecls : List Decl)
    (seed : List String) : List String :=
  let rec loop (fuel : Nat) (keep : List String) : List String :=
    match fuel with
    | 0 => keep
    | fuel + 1 =>
      let kept := implDecls.filter (fun d =>
        match declName? d with
        | some n => keep.contains n
        | none => false)
      let next := (keep ++ (kept.flatMap declRefs).filter isSyntheticImplName).eraseDups
      if next.length == keep.length then keep else loop fuel next
  loop (implDecls.length + 1) seed.eraseDups

/-- Drop synthetic impl-block accessor spec fns that no user-level decl
    transitively references. Non-synthetic decls (struct/enum/proofFn/
    execFn/user spec fns/mutualBlocks) are retained unchanged. -/
private def pruneUnreferencedImpls (decls : List Decl) : List Decl :=
  let (helpers, others) := decls.partition declIsSyntheticImpl
  let seed := (others.flatMap declRefs).filter isSyntheticImplName
  let kept := closeImplRefs helpers seed
  decls.filter (fun d =>
    if declIsSyntheticImpl d then
      match declName? d with
      | some n => kept.contains n
      | none => true
    else true)

def declsToBooleProgram (decls : List Decl) :
    BuildM (Array BCmd) := do
  -- Drop Verus-synthesised impl-block accessor spec fns that aren't
  -- transitively referenced by any user-level decl. Eager emission of every
  -- `Impl__N_arrow_*` bloats the output and slows verification; most tests
  -- use only a handful.
  let decls := pruneUnreferencedImpls decls
  let noParamFns := collectNoParamFnNamesFromDecls decls
  let projLayouts := buildProjLayouts decls
  let mutArgMap := collectMutArgMapFromDecls decls
  let sfMap := collectSpecFns decls
  let env := buildEnv decls noParamFns sfMap
  -- Detect whether any for-loop will be recovered
  let hasForLoop := declsHaveForLoop decls
  -- When for-loop recovery is active, skip translating iterator scaffolding declarations
  let filteredDecls := if hasForLoop then
    decls.filter fun d =>
      let name := declPrimaryName d
      !isForLoopScaffoldingDecl name
    else decls
  -- Translate user declarations first to discover which support names are needed
  let mut userCmds : Array BCmd := #[]
  for d in filteredDecls do
    let cmds ← declToBoole env projLayouts mutArgMap sfMap decls d
    userCmds := userCmds ++ cmds.toArray
  -- Support declarations are emitted from explicit requirements recorded
  -- during lowering, not from incidental free-variable references.
  let ctx ← get
  let supportNeeds := ctx.supportNeeds
  let supportCmds ← supportDeclCommands typToBooleType supportNeeds
  return supportCmds ++ userCmds

/-- Convenience: run the full translation pipeline and return the resulting
    BooleDDM commands, or an error string. -/
def translateDecls (decls : List Decl) : Except String (Array BCmd) :=
  match (declsToBooleProgram decls).run emptyCtx with
  | .ok (cmds, _) => .ok cmds
  | .error e => .error e

/-- Like `translateDecls` but also returns the build context for name resolution. -/
def translateDeclsWithCtx (decls : List Decl) : Except String (Array BCmd × BuildCtx) :=
  match (declsToBooleProgram decls).run emptyCtx with
  | .ok (cmds, ctx) => .ok (cmds, ctx)
  | .error e => .error e

/-- Like `translateDeclsWithCtx` but pre-registers prelude names so fvar
    indices align with Strata's `Program.globalContext` when the prelude is
    prepended to the output. -/
def translateDeclsWithPrelude (decls : List Decl) (preludeNames : Array String) :
    Except String (Array BCmd × BuildCtx) :=
  let initCtx := emptyCtx.addGlobalFreeVars preludeNames
  match (declsToBooleProgram decls).run initCtx with
  | .ok (cmds, ctx) => .ok (cmds, ctx)
  | .error e => .error e

/-- Extract the declared name from a BooleDDM command, if it has one. -/
def cmdDeclName? : BCmd → Option String
  | .command_fndecl _ name _ _ _ => some name.val
  | .command_fndef _ name _ _ _ _ _ _ => some name.val
  | .command_recfndefs _ _ => none  -- multiple names
  | .command_typedecl _ name _ => some name.val
  | .command_typesynonym _ name _ _ _ => some name.val
  | .command_datatypes _ _ => none  -- multiple names
  | .command_procedure _ name _ _ _ _ _ => some name.val
  | .command_axiom _ _ _ => none
  | .command_var _ bind => some (match bind with | .bind_mk _ name _ _ => name.val)
  | .command_distinct _ _ _ => none
  | .command_constdecl _ name _ _ => some name.val
  | .command_block _ _ => none

end Translate

end VerusLean.Boole
