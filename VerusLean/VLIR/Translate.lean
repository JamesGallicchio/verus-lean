/-
  VLIR to BooleDDM Direct Translation

  Translates the Verus-Lean IR (VLIR) directly to BooleDDM AST,
  bypassing the intermediate Strata Core representation.

  This is a rewrite of ToCore.lean that produces `BExpr`/`BStmt`/`BCmd`
  (from Builder.lean) instead of `CoreExpr`/`Core.Statement`/`Core.Decl`.

  The monad is `BuildM` (from Emit.lean), which tracks free/bound variable
  scopes for de Bruijn index resolution in BooleDDM nodes.
-/

import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Emit

namespace VerusLean

namespace Translate

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Emit

-- We intentionally do NOT `open VerusLean.Boole.Builder` because some of its
-- names (`fvar`, `bvar`, `app`, `eq`, `old`, …) conflict with Lean builtins
-- or BooleDDM constructors inside `mutual` blocks.  Instead we re-export
-- under the short prefix `Bld.*`.
namespace Bld
  export VerusLean.Boole.Builder (
    BExpr BType BStmt BCmd BBlock
    boolTy intTy strTy bvTy mapTy seqTy arrowTy tvarTy fvarTy unknownTy
    fvar bvar boolConst intConst bitvecConstNat bitvecConst
    ite eq neq app appN
    boolNot boolAnd boolOr boolImplies boolEquiv
    intAdd intSub intMul intDiv intMod intNeg
    intLe intLt intGe intGt
    bvAdd bvSub bvMul bvUDiv bvUMod bvSDiv bvSMod bvNeg
    bvAnd bvOr bvXor bvNot bvShl bvUShr
    bvUle bvUlt bvUge bvUgt bvSle bvSlt bvSge bvSgt
    mapGet mapSet seqLength old
    forallExpr existsExpr
    varStmt initStmt setStmt havocStmt
    assertStmt assumeStmt coverStmt callStmt blockStmt
    iteStmt whileStmt forToStmt exitStmt returnStmt
  )
end Bld
open Bld

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩
private def noLabel : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none
private def someLabel (s : String) : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  ann (some (.label default (ann s)))

/-! ## Type Aliases -/

abbrev VarEnv := Std.HashMap String Typ
abbrev BoundEnv := List (String × Typ)

structure MutArgInfo where
  idx : Nat
  ty : Typ

abbrev MutArgMap := Std.HashMap String (List MutArgInfo)

/-! ## Utilities -/

/-- Sanitize an identifier for Boole emission.
    First char: [A-Za-z_], rest: [A-Za-z0-9_'?!].
    Characters outside this set are replaced by `_`. -/
def sanitizeIdent (s : String) : String :=
  match s.toList with
  | [] => "_"
  | c :: cs =>
    let first := if c.isAlpha || c == '_' then c else '_'
    let rest := cs.map (fun c =>
      if c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!' then c else '_')
    let out := String.ofList (first :: rest)
    if out == "type" then "type_" else out

/-- Drop the leading namespace segment from a dotted/double-colon identifier. -/
def stripLeadingNamespace (s : String) : String :=
  let dropFirstSegment (sep : String) : Option String :=
    match s.splitOn sep with
    | _ :: rest@(_ :: _) => some (String.intercalate sep rest)
    | _ => none
  let dropLeadingModulePrefix : Option String :=
    match s.splitOn "_" with
    | p :: rest@(_ :: _) =>
      let startsUpper := match p.toList.head? with
        | some c => c.isUpper
        | none => false
      let alphaNum := p.toList.all (fun c => c.isAlpha || c.isDigit)
      if startsUpper && alphaNum then
        some (String.intercalate "_" rest)
      else
        none
    | _ => none
  (dropFirstSegment "." <|> dropFirstSegment "::" <|> dropLeadingModulePrefix).getD s

/-- Strip `_Impl__N_` segments from sanitized names. -/
private def stripImplSegment (name : String) : String :=
  let tryStrip (sep : String) : Option String :=
    match name.splitOn sep with
    | [before, after] =>
      let digits := after.toList.takeWhile Char.isDigit
      if digits.isEmpty then none
      else
        let rest := after.drop digits.length
        let rest := if rest.startsWith "_" then rest.drop 1 else rest
        if rest.isEmpty then some before
        else some s!"{before}_{rest}"
    | _ => none
  (tryStrip "_Impl__" <|> tryStrip "_impl__").getD name

def identToBoole (i : Ident) : String :=
  stripImplSegment (sanitizeIdent (stripLeadingNamespace i.toString))

def sanitizeVarName (s : String) : String :=
  sanitizeIdent (s.replace "%" "_pct_")

def usizeBitWidth : Nat := 64

def isSupportedBvWidth (w : Nat) : Bool :=
  w == 1 || w == 8 || w == 16 || w == 32 || w == 64

private def supportedBvWidths : List Nat := [1, 8, 16, 32, 64]

/-! ## Name Helpers -/

private def strataReservedTypeNames : List String :=
  ["Seq", "Set", "Map", "Multiset", "Triggers", "TriggerGroup"]

private def canonicalStdlibTypeName? (dt : Ident) : Option String :=
  let raw := dt.toString
  let rawLower := raw.toLower
  let short := sanitizeIdent (stripLeadingNamespace raw)
  if rawLower.contains "vstd" then
    if short == "Seq" && rawLower.contains "seq" then some "Seq"
    else if short == "Set" && rawLower.contains "set" then some "Set"
    else if short == "Multiset" && rawLower.contains "multiset" then some "Multiset"
    else none
  else
    none

def datatypeNameOf (dt : Ident) : String :=
  match canonicalStdlibTypeName? dt with
  | some name => name
  | none =>
    let name := sanitizeIdent (stripLeadingNamespace dt.toString)
    if strataReservedTypeNames.contains name then s!"Verus_{name}" else name

def structCtorNameOf (dt : Ident) : String :=
  datatypeNameOf dt ++ "_ctor"

def enumCtorNameOf (dt : Ident) (variant : String) : String :=
  datatypeNameOf dt ++ "_" ++ sanitizeIdent variant

def fieldAccessorNameOf (field : String) : String :=
  match field.toNat? with
  | some i => s!"_{i}"
  | none => sanitizeIdent field

def datatypeDestructorNameOf (dt : Ident) (field : String) : String :=
  s!"{datatypeNameOf dt}..{fieldAccessorNameOf field}"

def enumTesterNameOf (dt : Ident) (variant : String) : String :=
  let dtName := datatypeNameOf dt
  let ctorName := enumCtorNameOf dt variant
  s!"{dtName}..is{ctorName}"

def projFieldNameOf (dt : Ident) (variant field : String) : String :=
  if field == "_" then
    s!"{datatypeNameOf dt}_{sanitizeIdent variant}_0"
  else
    match field.toNat? with
    | some i => s!"{datatypeNameOf dt}_{sanitizeIdent variant}_{i}"
    | none =>
      let dtName := datatypeNameOf dt
      let variantName := sanitizeIdent variant
      if variantName.toLower == dtName.toLower then
        field
      else
        s!"{dtName}_{variantName}_{sanitizeIdent field}"

/-! ## Vec/Seq Name Recognition -/

def isVecTypeName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "Vec" || s.endsWith "vec"

def isVecLenSpecName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "spec_vec_len" || s.endsWith "Seq.len" || s.endsWith "seq.len"

def isVecLenExecName (name : Ident) : Bool :=
  let s := name.toString
  let hasAlloc := (s.find? "Alloc").isSome || (s.find? "alloc").isSome
  let hasVec := (s.find? "Vec").isSome || (s.find? "vec").isSome
  s.endsWith "len" && hasAlloc && hasVec

def isVecIndexSpecName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "Seq.index" || s.endsWith "seq.index"

def isVecIndexExecName (name : Ident) : Bool :=
  name.toString.endsWith "vec_index"

def isViewName (name : Ident) : Bool :=
  name.toString.endsWith ".view"

def isRangeTypeName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "range.range" || s.endsWith "range::range"

def isIteratorNextName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "next" && s.contains "iterator"

def isIntoIterName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "into_iter" && s.contains "collect"

def isGhostPervasiveCallName (fn : Ident) : Bool :=
  let s := fn.toString.toLower
  s.contains "pervasive" && s.contains "ghost_"

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

def isFuelVar : Exp → Bool
  | .Var name => name.startsWith "fuel%" || name.startsWith "fuel_"
  | _ => false

def normalizeCallArgs (args : List Exp) : List Exp :=
  args.filter (fun e => !isFuelVar e)

private def normalizeCallArgsForCallee (env : VarEnv) (fname : Ident) (args : List Exp) : List Exp :=
  let fnameStr := identToBoole fname
  let argsNoFuel := normalizeCallArgs args
  if hasNoParamFnMarker env fnameStr then
    argsNoFuel.filter (fun e =>
      match e with
      | .Unary (.Box .Int) (.Const (.Int 0)) => false
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
    let idx ← resolveFreeVar "Tuple"
    let a1 ← typToBooleType t1
    let a2 ← typToBooleType t2
    pure (fvarTy idx #[a1, a2])
  | .Bool => pure boolTy
  | .Int => pure intTy
  | .Nat => do
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

def bitWidthOfTyp : Typ → Option Nat
  | .UInt w | .SInt w => if isSupportedBvWidth w then some w else none
  | .Decorated _ ty => bitWidthOfTyp ty
  | _ => none

def bitInfoOfTyp : Typ → Option (Nat × Bool)
  | .UInt w => if isSupportedBvWidth w then some (w, false) else none
  | .SInt w => if isSupportedBvWidth w then some (w, true) else none
  | .Decorated _ ty => bitInfoOfTyp ty
  | _ => none

def isIntTyp : Typ → Bool
  | .Int => true
  | .Decorated _ ty => isIntTyp ty
  | _ => false

def isUnitLikeTyp : Typ → Bool
  | .Unit | .Empty => true
  | .Decorated _ ty => isUnitLikeTyp ty
  | _ => false

def bitTypOfInfo (w : Nat) (signed : Bool) : Typ :=
  if signed then Typ.SInt w else Typ.UInt w

def isSeqTyp : Typ → Bool
  | .Struct name _ => datatypeNameOf name == "Seq"
  | .Decorated _ ty => isSeqTyp ty
  | _ => false

def vecElemTyp? : Typ → Option Typ
  | .Struct name params =>
    if isVecTypeName name then params.head? else none
  | .Decorated _ ty => vecElemTyp? ty
  | _ => none

/-! ## Numeric Coercion -/

/-- Numeric type classification for coercion decisions. -/
inductive NumKind where
  | int
  | nat
  | bv (w : Nat) (signed : Bool)
  deriving DecidableEq, Repr

def numKindOfTyp? : Typ → Option NumKind
  | .Int => some .int
  | .Nat => some .nat
  | .UInt w => if isSupportedBvWidth w then some (.bv w false) else none
  | .SInt w => if isSupportedBvWidth w then some (.bv w true) else none
  | .Decorated _ ty => numKindOfTyp? ty
  | _ => none

def bvToIntCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_int_s" else s!"bv{w}_to_int_u"

def bvToNatCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_nat_s" else s!"bv{w}_to_nat_u"

def intToBvCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"int_to_bv{w}_s" else s!"int_to_bv{w}_u"

def bvWidenCastName (fromW toW : Nat) (signed : Bool) : String :=
  if signed then s!"bv{fromW}_to_bv{toW}_s" else s!"bv{fromW}_to_bv{toW}_u"

def isBvToIntCastName (s : String) : Bool :=
  s.endsWith "_to_int_u" || s.endsWith "_to_int_s"

def isBvToNatCastName (s : String) : Bool :=
  s.endsWith "_to_nat_u" || s.endsWith "_to_nat_s"

def isIntToBvCastName (s : String) : Bool :=
  s.startsWith "int_to_bv" && (s.endsWith "_u" || s.endsWith "_s")

def isBvWidenCastName (s : String) : Bool :=
  (s.startsWith "bv" && (s.find? "_to_bv").isSome && (s.endsWith "_u" || s.endsWith "_s"))

private def canPromoteBvWidths (fromW toW : Nat) : Bool :=
  isSupportedBvWidth fromW && isSupportedBvWidth toW && fromW <= toW

private def choosePromotionWidth? (w1 w2 : Nat) : Option Nat :=
  let w := max w1 w2
  if canPromoteBvWidths w1 w && canPromoteBvWidths w2 w then some w else none

private def chooseBitPromotionInfo?
    (lhsInfo rhsInfo : Nat × Bool) : Option (Nat × Bool) :=
  let (w1, s1) := lhsInfo
  let (w2, s2) := rhsInfo
  if s1 == s2 then
    (choosePromotionWidth? w1 w2).map (fun w => (w, s1))
  else
    none

/-- Resolve a cast function name to a BExpr (free variable). -/
private def castFnExpr (name : String) : BuildM BExpr := do
  let idx ← resolveFreeVar name
  pure (Bld.fvar idx)

/-- Apply a unary cast function. -/
private def applyCast (castName : String) (e : BExpr) : BuildM BExpr := do
  let fn ← castFnExpr castName
  pure (Bld.app fn e)

private def castExprToWiderBvB (fromW toW : Nat) (signed : Bool) (e : BExpr) : BuildM BExpr := do
  if fromW == toW then pure e
  else applyCast (bvWidenCastName fromW toW signed) e

/-- Insert a single numeric coercion. Returns the expression unchanged when
    no coercion is needed. -/
def coerceNumeric (src? target? : Option NumKind) (e : BExpr) :
    BuildM BExpr :=
  match src?, target? with
  | _, none | none, _ => pure e
  | some src, some target =>
    if src == target then pure e
    else match src, target with
    | .bv w s, .int => applyCast (bvToIntCastName w s) e
    | .bv w s, .nat => applyCast (bvToNatCastName w s) e
    | .nat, .int => applyCast "nat_to_int" e
    | .int, .bv w s => applyCast (intToBvCastName w s) e
    | .nat, .bv w s => do
      let eInt ← applyCast "nat_to_int" e
      applyCast (intToBvCastName w s) eInt
    | .bv sw ss, .bv tw ts =>
      if ss == ts && canPromoteBvWidths sw tw then
        castExprToWiderBvB sw tw ss e
      else do
        let eInt ← applyCast (bvToIntCastName sw ss) e
        applyCast (intToBvCastName tw ts) eInt
    | .int, .nat => pure e
    | .int, .int | .nat, .nat => pure e

/-- Coerce between bitvector widths when both source and target are known. -/
def coerceBvBv (srcInfo? targetInfo? : Option (Nat × Bool)) (e : BExpr) :
    BuildM BExpr := do
  match srcInfo?, targetInfo? with
  | some (sw, ss), some (tw, ts) =>
    if sw == tw && ss == ts then pure e
    else if ss == ts && canPromoteBvWidths sw tw then
      castExprToWiderBvB sw tw ss e
    else do
      let eInt ← applyCast (bvToIntCastName sw ss) e
      applyCast (intToBvCastName tw ts) eInt
  | _, _ => pure e

/-! ## Known Function Registry -/

private def knownFnSignature? (fname : String) : Option (List Typ × Typ) :=
  let t := Typ.TypParam "T"
  let a := Typ.TypParam "A"
  let b := Typ.TypParam "B"
  let seqT := Typ.Struct (.str (.str .anonymous "vstd") "Seq") [t]
  let setT := Typ.Struct (.str (.str .anonymous "vstd") "Set") [t]
  let vecT := Typ.Struct (.str (.str .anonymous "vstd") "Vec") [t]
  let mapAB := Typ.Struct (.str (.str .anonymous "vstd") "Map") [a, b]
  let registry : List (String × (List Typ × Typ)) :=
    [ ("Seq_index",        ([seqT, .Int], t))
    , ("Seq_update",       ([seqT, .Int, t], seqT))
    , ("Seq_push",         ([seqT, t], seqT))
    , ("Seq_take",         ([seqT, .Int], seqT))
    , ("Seq_skip",         ([seqT, .Int], seqT))
    , ("Seq_add",          ([seqT, seqT], seqT))
    , ("Seq_first",        ([seqT], t))
    , ("Seq_last",         ([seqT], t))
    , ("Seq_subrange",     ([seqT, .Int, .Int], seqT))
    , ("Seq_lib_contains", ([seqT, t], .Bool))
    , ("Seq_lib_drop_last",([seqT], seqT))
    , ("Seq_lib_remove",   ([seqT, .Int], seqT))
    , ("Seq_len",          ([seqT], .Nat))
    , ("Seq_lib_insert",   ([seqT, .Int, t], seqT))
    , ("Seq_new",          ([.Nat, .SpecFn [.Int] t], seqT))
    , ("Seq_lib_map",      ([Typ.Struct (.str (.str .anonymous "vstd") "Seq") [a], .SpecFn [.Int, a] b],
                            Typ.Struct (.str (.str .anonymous "vstd") "Seq") [b]))
    , ("Seq_lib_map_values",([Typ.Struct (.str (.str .anonymous "vstd") "Seq") [a], .SpecFn [a] b],
                             Typ.Struct (.str (.str .anonymous "vstd") "Seq") [b]))
    , ("Seq_lib_filter",   ([seqT, .SpecFn [t] .Bool], seqT))
    , ("Seq_lib_sort_by",  ([seqT, .SpecFn [t, t] .Bool], seqT))
    , ("Seq_lib_to_set",   ([seqT], setT))
    , ("Set_finite",       ([setT], .Bool))
    , ("nat_to_int",       ([.Nat], .Int))
    , ("int_to_nat",       ([.Int], .Nat))
    , ("Vec_len",          ([vecT], .UInt usizeBitWidth))
    , ("Vec_index",        ([vecT, .UInt usizeBitWidth], t))
    , ("Vec_view",         ([vecT], seqT))
    , ("Set_contains",     ([setT, a], .Bool))
    , ("Map_index",        ([mapAB, a], b))
    ]
  -- Also check cast function signatures
  let castSig := supportedBvWidths.findSome? (fun w =>
    if fname == s!"bv{w}_to_int_u" then some ([.UInt w], .Int)
    else if fname == s!"bv{w}_to_int_s" then some ([.SInt w], .Int)
    else if fname == s!"bv{w}_to_nat_u" then some ([.UInt w], .Nat)
    else if fname == s!"bv{w}_to_nat_s" then some ([.SInt w], .Nat)
    else if fname == s!"int_to_bv{w}_u" then some ([.Int], .UInt w)
    else if fname == s!"int_to_bv{w}_s" then some ([.Int], .SInt w)
    else none)
  (registry.find? (fun (n, _) => n == fname) |>.map Prod.snd) <|> castSig

private def lookupKnownFnRetType (fname : String) : Option Typ :=
  (knownFnSignature? fname).map Prod.snd

private def lookupKnownFnParamType (fname : String) (idx : Nat) : Option Typ := do
  let (params, _) ← knownFnSignature? fname
  params.drop idx |>.head?

/-! ## Full lookups combining env + known functions -/

private def lookupFnRetTypeFull (env : VarEnv) (fname : String) : Option Typ :=
  lookupFnRetType env fname <|> lookupKnownFnRetType fname

private def lookupFnParamTypeFull (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  lookupFnParamType env fname idx <|> lookupKnownFnParamType fname idx

/-! ## Bit-width Inference -/

private def constIntExprVal? : Exp → Option Int
  | .Const (.Int i) => some i
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

/-! ## Expression Substitution -/

private partial def expVarRefs : Exp → List String :=
  let merge (xs : List (List String)) : List String := (xs.foldl (· ++ ·) []).eraseDups
  fun
  | .Const _ => []
  | .Var x => [x]
  | .Call _ _ args => merge (args.map expVarRefs)
  | .CallLambda body args => (expVarRefs body ++ merge (args.map expVarRefs)).eraseDups
  | .StructCtor _ fields => merge <| fields.map (fun (_, e) => expVarRefs e)
  | .EnumCtor _ _ data => merge <| data.map (fun (_, e) => expVarRefs e)
  | .TupleCtor _ data => merge (data.map expVarRefs)
  | .Unary _ e => expVarRefs e
  | .Binary _ e1 e2 => (expVarRefs e1 ++ expVarRefs e2).eraseDups
  | .If c t f => (expVarRefs c ++ expVarRefs t ++ expVarRefs f).eraseDups
  | .Bind (.Let _ _ e) body => (expVarRefs e ++ expVarRefs body).eraseDups
  | .Bind (.Quant _ _ trigs) body =>
    merge ((trigs.map (fun g => merge <| g.map expVarRefs)) ++ [expVarRefs body])
  | .Bind (.Lambda _) body => expVarRefs body
  | .ArrayLiteral elems => merge (elems.map expVarRefs)
  | .MatchBlock (scrut, _) body => (expVarRefs scrut ++ expVarRefs body).eraseDups

private def freshenedName (base : String) (used : List String) : String :=
  if !used.contains base then base
  else
    let rec go : List Nat → String
      | [] => s!"{base}_fresh"
      | i :: rest =>
        let cand := s!"{base}_{i}"
        if used.contains cand then go rest else cand
    go (List.range (used.length + 1))

private def triggerVarRefs (trigs : List (List Exp)) : List String :=
  let flatten (xs : List (List String)) : List String := (xs.foldl (· ++ ·) []).eraseDups
  flatten <| trigs.map (fun g => flatten <| g.map expVarRefs)

mutual
partial def substExp (name : String) (rhs : Exp) : Exp → Exp
  | .Const c => .Const c
  | .Var x => if x == name then rhs else .Var x
  | .Call fn typs exps => .Call fn typs (exps.map (substExp name rhs))
  | .CallLambda body args =>
    .CallLambda (substExp name rhs body) (args.map (substExp name rhs))
  | .StructCtor dt fields =>
    .StructCtor dt (fields.map fun (n, e) => (n, substExp name rhs e))
  | .EnumCtor dt variant data =>
    .EnumCtor dt variant (data.map fun (n, e) => (n, substExp name rhs e))
  | .TupleCtor size data =>
    .TupleCtor size (data.map (substExp name rhs))
  | .Unary .Old e => .Unary .Old e
  | .Unary op e => .Unary op (substExp name rhs e)
  | .Binary op e1 e2 => .Binary op (substExp name rhs e1) (substExp name rhs e2)
  | .If c t f => .If (substExp name rhs c) (substExp name rhs t) (substExp name rhs f)
  | .Bind bind body =>
    match bind with
    | .Let v ty e =>
      let e' := substExp name rhs e
      if v == name then .Bind (.Let v ty e') body
      else
        let rhsRefs := expVarRefs rhs
        if rhsRefs.contains v then
          let v' := freshenedName v (rhsRefs ++ expVarRefs body ++ [name])
          let bodyRenamed := substExp v (.Var v') body
          .Bind (.Let v' ty e') (substExp name rhs bodyRenamed)
        else
          .Bind (.Let v ty e') (substExp name rhs body)
    | .Quant q vars trigs =>
      if vars.any (fun (v, _) => v == name) then .Bind (.Quant q vars trigs) body
      else
        let rhsRefs := expVarRefs rhs
        let (vars', trigs', body') := renameBinderPack vars trigs body rhsRefs [name]
        let trigs'' := trigs'.map (fun g => g.map (substExp name rhs))
        .Bind (.Quant q vars' trigs'') (substExp name rhs body')
    | .Lambda vars =>
      if vars.any (fun (v, _) => v == name) then .Bind (.Lambda vars) body
      else
        let rhsRefs := expVarRefs rhs
        let (vars', _, body') := renameBinderPack vars [] body rhsRefs [name]
        .Bind (.Lambda vars') (substExp name rhs body')
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (substExp name rhs))
  | .MatchBlock scrut body =>
    let (e, t) := scrut
    .MatchBlock (substExp name rhs e, t) (substExp name rhs body)

private partial def renameBinderPack
    (vars : List (String × Typ))
    (trigs : List (List Exp))
    (body : Exp)
    (rhsRefs : List String)
    (avoid : List String) :
    (List (String × Typ) × List (List Exp) × Exp) :=
  let rec go
      (rest : List (String × Typ))
      (used : List String)
      (trigsAcc : List (List Exp))
      (bodyAcc : Exp)
      (revVars : List (String × Typ)) :
      (List (String × Typ) × List (List Exp) × Exp) :=
    match rest with
    | [] => (revVars.reverse, trigsAcc, bodyAcc)
    | (v, ty) :: tail =>
      if rhsRefs.contains v then
        let v' := freshenedName v used
        let renameExpr := substExp v (.Var v')
        let trigs' := trigsAcc.map (fun g => g.map renameExpr)
        let body' := renameExpr bodyAcc
        go tail (v' :: used) trigs' body' ((v', ty) :: revVars)
      else
        go tail (v :: used) trigsAcc bodyAcc ((v, ty) :: revVars)
  go vars
    (avoid ++ rhsRefs ++ vars.map Prod.fst ++ expVarRefs body ++ triggerVarRefs trigs)
    trigs body []
end

def substExps (subs : List (String × Exp)) (e : Exp) : Exp :=
  subs.foldl (fun acc (n, rhs) => substExp n rhs acc) e

/-! ## Statement Substitution -/

partial def substStm (name : String) (rhs : Exp) : Stm → Stm
  | .Call fn typs args => .Call fn typs (args.map (substExp name rhs))
  | .Assert e => .Assert (substExp name rhs e)
  | .AssertBitVector reqs ens =>
    .AssertBitVector (reqs.map (substExp name rhs)) (ens.map (substExp name rhs))
  | .AssertQuery mode body => .AssertQuery mode (substStm name rhs body)
  | .AssertCompute e => .AssertCompute (substExp name rhs e)
  | .AssertLean e => .AssertLean (substExp name rhs e)
  | .Assume e => .Assume (substExp name rhs e)
  | .Assign lhs lhsTy e lhsIsInit =>
    .Assign lhs lhsTy (substExp name rhs e) lhsIsInit
  | .DeadEnd stm => .DeadEnd (substStm name rhs stm)
  | .Return e => .Return (e.map (substExp name rhs))
  | .BreakOrContinue label isBreak => .BreakOrContinue label isBreak
  | .If cond b1 b2 =>
    .If (substExp name rhs cond) (substStm name rhs b1) (b2.map (substStm name rhs))
  | .Loop isFor label cond body invs decrease =>
    let cond' := cond.map (fun (s, e) => (substStm name rhs s, substExp name rhs e))
    let invs' := invs.map (fun inv => { inv with body := substExp name rhs inv.body })
    let decrease' := decrease.map (substExp name rhs)
    .Loop isFor label cond' (substStm name rhs body) invs' decrease'
  | .OpenInvariant stm => .OpenInvariant (substStm name rhs stm)
  | .ClosureInner body => .ClosureInner (substStm name rhs body)
  | .Block stms => .Block (stms.map (substStm name rhs))
  | .Reveal fn fuel => .Reveal fn fuel

partial def renameStmVar (src dst : String) : Stm → Stm :=
  substStm src (.Var dst)

def applyNameSubstsExp (subs : List (String × String)) (e : Exp) : Exp :=
  subs.foldl (fun acc (src, dst) => substExp src (.Var dst) acc) e

def applyNameSubstsStm (subs : List (String × String)) (s : Stm) : Stm :=
  subs.foldl (fun acc (src, dst) => renameStmVar src dst acc) s

/-! ## Temporary Inlining -/

partial def stripSingletonBlocks : Stm → Stm
  | .Block [s] => stripSingletonBlocks s
  | s => s

def isTempName (s : String) : Bool :=
  if s.startsWith "tmp" then
    let tail := s.drop 3
    !tail.isEmpty && tail.all Char.isDigit
  else
    false

def lvalueVarName? : LValue → Option String
  | .Var s => some s
  | _ => none

private def isPureBuiltinCallExp : Exp → Bool
  | .Call fn _ _ =>
    let fn := CallFun.name fn
    isViewName fn || isVecLenSpecName fn || isVecLenExecName fn
      || isVecIndexSpecName fn || isVecIndexExecName fn
  | _ => false

def tempAssignFromPrefix : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name =>
        if !isTempName name then none
        else match rhs with
          | .Call _ _ _ => if isPureBuiltinCallExp rhs then some (name, rhs) else none
          | _ => some (name, rhs)
      | none => none
    | _ => none

def guardTempAssignFromPrefix : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name => if isTempName name then some (name, rhs) else none
      | none => none
    | _ => none

def dropCondTempAssignFromPrefix : Stm → Option String
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name =>
        if !isTempName name then none
        else match rhs with
          | .Call _ _ _ => if isPureBuiltinCallExp rhs then some name else none
          | _ => some name
      | none => none
    | _ => none

def isEmptyElse (b2 : Option Stm) : Bool :=
  match b2 with
  | none => true
  | some (Stm.Block []) => true
  | _ => false

def breakGuardFromPrefix : Stm → Option Exp
  | s =>
    match stripSingletonBlocks s with
    | .If (.Unary .Not guard) (.BreakOrContinue none true) b2 =>
      if isEmptyElse b2 then some guard else none
    | _ => none

def splitGuardTempPrefix (stms : List Stm) : List (String × Exp) × List Stm :=
  let rec go (subsRev : List (String × Exp)) (rest : List Stm) :
      List (String × Exp) × List Stm :=
    match rest with
    | s :: tail =>
      match guardTempAssignFromPrefix s with
      | some sub => go (sub :: subsRev) tail
      | none => (subsRev.reverse, rest)
    | [] => (subsRev.reverse, [])
  go [] stms

def splitDropCondTempPrefix (stms : List Stm) : List String × List Stm :=
  let rec go (namesRev : List String) (rest : List Stm) :
      List String × List Stm :=
    match rest with
    | s :: tail =>
      match dropCondTempAssignFromPrefix s with
      | some n => go (n :: namesRev) tail
      | none => (namesRev.reverse, rest)
    | [] => (namesRev.reverse, [])
  go [] stms

def assignFromPrefix : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name => some (name, rhs)
      | none => none
    | _ => none

def splitAssignPrefix (stms : List Stm) : List (String × Exp) × List Stm :=
  let rec go (subsRev : List (String × Exp)) (rest : List Stm) :
      List (String × Exp) × List Stm :=
    match rest with
    | s :: tail =>
      match assignFromPrefix s with
      | some sub => go (sub :: subsRev) tail
      | none => (subsRev.reverse, rest)
    | [] => (subsRev.reverse, [])
  go [] stms

partial def flattenSeqBlocks : List Stm → List Stm
  | [] => []
  | (.Block stms) :: rest => flattenSeqBlocks stms ++ flattenSeqBlocks rest
  | s :: rest => s :: flattenSeqBlocks rest

def extractLoopGuardFromBody : Stm → Option (Exp × Stm)
  | .Block stms =>
    let linear := (flattenSeqBlocks stms).map stripSingletonBlocks
    let (subs, rest) := splitGuardTempPrefix linear
    match rest with
    | s :: tail =>
      match breakGuardFromPrefix s with
      | some guard => some (substExps subs guard, Stm.Block tail)
      | none => none
    | [] => none
  | _ => none

private partial def isEmptyProofShell : Stm → Bool
  | .Block [] => true
  | .Block [s] => isEmptyProofShell s
  | _ => false

mutual
  private partial def recoverComputeProofStm : Stm → Stm
    | .AssertQuery mode body => .AssertQuery mode (recoverComputeProofStm body)
    | .DeadEnd stm => .DeadEnd (recoverComputeProofStm stm)
    | .If cond b1 b2 =>
      .If cond (recoverComputeProofStm b1) (b2.map recoverComputeProofStm)
    | .Loop isFor label cond body invs decrease =>
      let cond' := cond.map (fun (s, e) => (recoverComputeProofStm s, e))
      .Loop isFor label cond' (recoverComputeProofStm body) invs decrease
    | .OpenInvariant stm => .OpenInvariant (recoverComputeProofStm stm)
    | .ClosureInner body => .ClosureInner (recoverComputeProofStm body)
    | .Block stms => .Block (recoverComputeProofs stms)
    | s => s

  private partial def recoverComputeProofs : List Stm → List Stm
    | proofShell :: (.Assume e) :: rest =>
      if isEmptyProofShell proofShell then
        .AssertCompute e :: recoverComputeProofs rest
      else
        recoverComputeProofStm proofShell :: recoverComputeProofs ((.Assume e) :: rest)
    | s :: rest => recoverComputeProofStm s :: recoverComputeProofs rest
    | [] => []
end

private partial def expMentionsVar (target : String) : Exp → Bool
  | .Var x => x == target
  | .Call _ _ args => args.any (expMentionsVar target)
  | .CallLambda body args =>
    expMentionsVar target body || args.any (expMentionsVar target)
  | .StructCtor _ fields => fields.any (fun (_, e) => expMentionsVar target e)
  | .EnumCtor _ _ fields => fields.any (fun (_, e) => expMentionsVar target e)
  | .TupleCtor _ elems => elems.any (expMentionsVar target)
  | .Unary _ e => expMentionsVar target e
  | .Binary _ e1 e2 => expMentionsVar target e1 || expMentionsVar target e2
  | .If c t f => expMentionsVar target c || expMentionsVar target t || expMentionsVar target f
  | .Bind (.Let _ _ e) body => expMentionsVar target e || expMentionsVar target body
  | .Bind (.Quant _ _ _) body => expMentionsVar target body
  | .Bind (.Lambda _) body => expMentionsVar target body
  | .ArrayLiteral elems => elems.any (expMentionsVar target)
  | .MatchBlock (scrut, _) body => expMentionsVar target scrut || expMentionsVar target body
  | .Const _ => false

private partial def stmMentionsVar (target : String) : Stm → Bool
  | .Call _ _ args => args.any (expMentionsVar target)
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expMentionsVar target e
  | .AssertBitVector reqs enss =>
    reqs.any (expMentionsVar target) || enss.any (expMentionsVar target)
  | .AssertQuery _ body => stmMentionsVar target body
  | .Assign lhs _ rhs _ =>
    (match lvalueVarName? lhs with | some n => n == target | none => false) ||
    expMentionsVar target rhs
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => stmMentionsVar target s
  | .Reveal .. => false
  | .Return e? => e?.map (expMentionsVar target) |>.getD false
  | .BreakOrContinue _ _ => false
  | .If cond b1 b2 =>
    expMentionsVar target cond ||
      stmMentionsVar target b1 ||
      (b2.map (stmMentionsVar target)).getD false
  | .Loop _ _ cond body invs decrease =>
    let condM := match cond with
      | some (s, e) => stmMentionsVar target s || expMentionsVar target e
      | none => false
    condM || invs.any (fun inv => expMentionsVar target inv.body) ||
      decrease.any (expMentionsVar target) || stmMentionsVar target body
  | .Block stms => stms.any (stmMentionsVar target)

mutual
partial def inlineTempsInStm : Stm → Stm
  | .AssertQuery mode body => .AssertQuery mode (inlineTempsInStm body)
  | .DeadEnd stm => .DeadEnd (inlineTempsInStm stm)
  | .If cond b1 b2 => .If cond b1 b2
  | .Loop isFor label cond body invs decrease =>
    let cond' := cond
    let body' := match body with
      | .Block stms => .Block (inlineTemps stms)
      | _ => inlineTempsInStm body
    .Loop isFor label cond' body' invs decrease
  | .OpenInvariant stm => .OpenInvariant (inlineTempsInStm stm)
  | .ClosureInner body => .ClosureInner (inlineTempsInStm body)
  | .Block stms => .Block (inlineTemps stms)
  | .Reveal fn fuel => .Reveal fn fuel
  | s => s

partial def inlineTemps : List Stm → List Stm
  | [] => []
  | stm :: rest =>
    let rest' := inlineTemps rest
    match tempAssignFromPrefix stm with
    | some (lhs, rhs) =>
      if rest'.any (stmMentionsVar lhs) then
        rest'.map (substStm lhs rhs)
      else
        inlineTempsInStm stm :: rest'
    | none => inlineTempsInStm stm :: rest'
end

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

def shouldDropAssignAsForLoopScaffolding (lhs : LValue) : Bool :=
  match lvalueVarName? lhs with
  | some name => name.startsWith "VERUS_ghost_" || name == "VERUS_loop_result"
  | none => false

def shouldDropForLoopScaffoldingLocal (name : String) : Bool :=
  name.startsWith "VERUS_" || name.startsWith "decrease"

def isForLoopScaffoldingVar (name : String) : Bool :=
  name.startsWith "VERUS_" || name.startsWith "tmp" || name.startsWith "decrease"

/-! ## For-Loop Recovery -/

/-- Check whether an identifier looks like an `Iterator::next` call. -/
private def isIteratorNextCall : Stm → Bool
  | .Call fn _ _ => isIteratorNextName fn
  | _ => false

/-- Check whether an expression is `IsVariant(Option, Some, ...)`. -/
private def isOptionIsSomeCheck : Exp → Bool
  | .Unary (.IsVariant dt "Some") _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  | _ => false

/-- Check whether an expression is `Proj(Option, Some, 0, ...)` (i.e. unwrapping Some). -/
private def isOptionSomeProj : Exp → Bool
  | .Unary (.Proj dt "Some" "0" _ _) _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  | _ => false

/-- Flatten nested singleton blocks. -/
private partial def flattenBody : Stm → List Stm
  | .Block stms => stms.flatMap flattenBody
  | s => [s]

/-- Structure holding extracted for-loop information from the loop body. -/
structure ForLoopBodyInfo where
  loopVarName : String
  loopVarTy : Typ
  userBody : List Stm
deriving Repr

/--
  Try to extract for-loop structure from the loop body.

  The for-loop body after Verus desugaring follows this pattern (with some nesting):
  1. Call Iterator::next on the exec iterator
  2. If Option::is_Some(result):
       - Assign loop_var := Option::Some_0(result)
       - User body
     Else:
       - Break
  3. Iterator update assignments

  We try to find the If with the Option check, extract the loop variable assignment
  and the user body from the then-branch.
-/
private partial def matchForLoopBody? (body : Stm) : Option ForLoopBodyInfo := do
  let stms := flattenBody body
  -- Find the If statement with the Option::is_Some check
  let (ifStm, postIfStms) ← findOptionIf stms
  -- Extract from the if statement
  let (cond, thenBranch, elseBranch) ← match ifStm with
    | .If c b1 b2 => some (c, b1, b2)
    | _ => none
  -- Verify condition is Option::is_Some
  guard (isOptionIsSomeCheck cond)
  -- Verify else branch contains a break
  guard (hasBreak elseBranch)
  -- First try: look for the loop variable assignment inside the then-branch
  let thenStms := flattenBody thenBranch
  match extractLoopVarFromThen thenStms with
  | some (loopVarName, loopVarTy, userBodyInThen) =>
    let userBody := userBodyInThen ++ filterScaffoldingStms postIfStms
    some { loopVarName, loopVarTy, userBody }
  | none =>
    -- Second try: the loop variable might be assigned AFTER the If statement
    -- Pattern: If(..., Block[VERUS_loop_val := ..., VERUS_loop_next := ...], Block[Break])
    --          i := VERUS_loop_next (or VERUS_loop_val)
    --          <user body>
    match findLoopVarAfterIf postIfStms with
    | some (loopVarName, loopVarTy, userBody) =>
      some { loopVarName, loopVarTy, userBody }
    | none => none
where
  findOptionIf (stms : List Stm) : Option (Stm × List Stm) :=
    let rec go (rest : List Stm) : Option (Stm × List Stm) :=
      match rest with
      | [] => none
      | s :: tail =>
        match s with
        | .If cond _ _ =>
          if isOptionIsSomeCheck cond then some (s, tail)
          else go tail
        | .Block inner =>
          match go (flattenBody (.Block inner)) with
          | some (ifS, innerRest) => some (ifS, innerRest ++ tail)
          | none => go tail
        | _ => go tail
    go stms

  hasBreak : Option Stm → Bool
    | some (.BreakOrContinue _ true) => true
    | some (.Block stms) => stms.any fun
      | .BreakOrContinue _ true => true
      | _ => false
    | _ => false

  extractLoopVarFromThen (stms : List Stm) : Option (String × Typ × List Stm) :=
    match stms with
    | [] => none
    | s :: rest =>
      match s with
      | .Assign lhs ty rhs _ =>
        match lvalueVarName? lhs with
        | some name =>
          if isOptionSomeProj rhs && !isForLoopScaffoldingVar name then
            -- Direct assignment: loopVar := Option::Some_0(...)
            some (name, ty, filterScaffoldingStms rest)
          else
            extractLoopVarFromThen rest
        | none => extractLoopVarFromThen rest
      | _ => extractLoopVarFromThen rest

  findLoopVarAfterIf (stms : List Stm) : Option (String × Typ × List Stm) :=
    match stms with
    | [] => none
    | s :: rest =>
      match s with
      | .Assign lhs ty _rhs _ =>
        match lvalueVarName? lhs with
        | some name =>
          if !isForLoopScaffoldingVar name then
            -- Found the loop variable assignment (e.g. i := VERUS_loop_next)
            some (name, ty, filterScaffoldingStms rest)
          else
            findLoopVarAfterIf rest
        | none => findLoopVarAfterIf rest
      | _ => findLoopVarAfterIf rest

  filterScaffoldingStms (stms : List Stm) : List Stm :=
    stms.filter fun
      | .Assign lhs _ _ _ =>
        match lvalueVarName? lhs with
        | some name => !isForLoopScaffoldingVar name
        | none => true
      | .Call fn _ _ =>
        !(isIteratorNextName fn || isIntoIterName fn || isGhostPervasiveCallName fn)
      | .Assume (.Const (.Bool false)) => false
      | _ => true

/--
  Find the Range start/end from pre-loop context.

  Before the for-loop, Verus generates:
  - Assign(tmp_start, startExpr)
  - Call(vec.len, ...) or similar → tmp_end
  - Assign(VERUS_iter, StructCtor(Range, [("start", startExpr), ("end", endExpr)]))
  - Call(into_iter, ...) → iterator
  - Various iterator setup assignments

  We look for the StructCtor(Range, ...) to extract start/end.
-/
structure ForLoopRangeInfo where
  startExp : Exp
  endExp : Exp
  iterVarName : Option String := none
deriving Repr

/-- Strip Box/Unbox wrappers from an expression. -/
private partial def stripBoxUnbox : Exp → Exp
  | .Unary (.Box _) e => stripBoxUnbox e
  | .Unary (.Unbox _) e => stripBoxUnbox e
  | e => e

/--
  Scan a list of statements preceding the for-loop to find the Range constructor
  and extract the start/end expressions.
-/
private partial def findRangeSetup? (preStms : List Stm) : Option ForLoopRangeInfo := do
  -- Build substitution map from temp assignments
  let subs := preStms.filterMap fun
    | .Assign lhs _ rhs _ =>
      match lvalueVarName? lhs with
      | some name => some (name, rhs)
      | none => none
    | _ => none
  -- Find the Range StructCtor assignment
  let rangeInfo ← preStms.findSome? fun
    | .Assign _lhs _ (.StructCtor dt fields) _ =>
      if isRangeTypeName dt then
        match fields with
        | [("start", startE), ("end", endE)] =>
          some (stripBoxUnbox (substExps subs startE), stripBoxUnbox (substExps subs endE))
        | _ => none
      else none
    | _ => none
  some { startExp := rangeInfo.1, endExp := rangeInfo.2 }

/--
  Check if an expression is a ghost iterator reference pattern:
  `If(IsVariant(Option, Some, ghost_peek_next(iter)),
      Proj(Option, Some, 0, ghost_peek_next(iter)),
      arbitrary())`
  This pattern represents "the current value of the for-loop iterator",
  which in a recovered for-loop is just the loop variable itself.
-/
private partial def isGhostIteratorPeekPattern : Exp → Bool
  | .If cond thenE _elseE =>
    isOptionIsSomeCheck cond && isOptionSomeProj thenE
  | _ => false

/--
  Check if an invariant expression is a "ghost iterator" internal invariant
  (exec_invariant, ghost_advance, ghost_ensures, etc.) that should be dropped.
-/
private partial def isGhostIteratorInvariant : Exp → Bool
  | .Unary (.Unbox _) e => isGhostIteratorInvariant e
  | .Unary (.Box _) e => isGhostIteratorInvariant e
  | .Call fn _ _ =>
    let s := (CallFun.name fn).toString.toLower
    s.contains "forloopghostiterator" || s.contains "ghost_invariant" ||
    s.contains "exec_invariant" || s.contains "ghost_ensures" ||
    s.contains "ghost_advance"
  | .Unary _ e => isGhostIteratorInvariant e
  | _ => false

/--
  Rewrite a for-loop invariant expression.

  User-written invariants in a for-loop are wrapped as:
  `Bind(Let("i", ty, <ghost_peek_expr>), <actual_invariant>)`

  where `<ghost_peek_expr>` computes the current iterator value through the ghost
  iterator machinery. In a recovered for-loop, the loop variable `i` is bound
  directly, so we strip this outer let-binding.

  Within the actual invariant body, references to the loop variable are already
  just `Var("i")`, so no further rewriting is needed.
-/
private partial def rewriteForLoopInvariant (loopVar : String) : Exp → Exp
  | .Bind (.Let v _ty rhs) body =>
    if v == loopVar then
      let isGhostPeek := isGhostPeekRhs rhs
      if isGhostPeek then
        -- Strip the ghost peek Let binding but substitute the loop variable
        -- into the body so references to `v` resolve to the for-loop's `i`.
        substExp v (.Var loopVar) body
      else .Bind (.Let v _ty (rewriteForLoopInvariant loopVar rhs)) (rewriteForLoopInvariant loopVar body)
    else
      -- Non-loop-var Let: check if the *rhs* is a ghost peek pattern
      let isGhostPeek := isGhostPeekRhs rhs
      if isGhostPeek then
        substExp v (.Var loopVar) (rewriteForLoopInvariant loopVar body)
      else
        .Bind (.Let v _ty (rewriteForLoopInvariant loopVar rhs)) (rewriteForLoopInvariant loopVar body)
  | .Unary (.Unbox _) e => rewriteForLoopInvariant loopVar e
  | .Unary (.Box _) e => rewriteForLoopInvariant loopVar e
  | e => e
where
  isGhostPeekRhs : Exp → Bool
    | .Bind (.Let _ _ innerRhs) innerBody =>
      hasGhostPeekCall innerRhs || isGhostIteratorPeekPattern innerBody || isGhostPeekRhs innerBody
    | .If cond thenE _elseE =>
      isOptionIsSomeCheck cond && isOptionSomeProj thenE
    | .Unary (.Unbox _) e | .Unary (.Box _) e => isGhostPeekRhs e
    | .Call fn _ _ =>
      let s := (CallFun.name fn).toString.toLower
      s.contains "ghost_peek" || s.contains "ghost_peek_next"
    | _ => false

  hasGhostPeekCall : Exp → Bool
    | .Call fn _ _ =>
      let s := (CallFun.name fn).toString.toLower
      s.contains "ghost_peek" || s.contains "ghost_peek_next"
    | .Unary _ e => hasGhostPeekCall e
    | _ => false

/--
  Process for-loop invariants:
  1. Drop system-generated ghost iterator invariants
  2. Rewrite user invariants to strip the ghost peek let-binding
-/
private def processForLoopInvariants (loopVar : String) (invs : List LoopInvariant)
    : List LoopInvariant :=
  invs.filterMap fun inv =>
    if isGhostIteratorInvariant inv.body then none
    else
      let rewritten := rewriteForLoopInvariant loopVar inv.body
      some { inv with body := rewritten }

/--
  Process for-loop decrease expressions, similarly stripping ghost iterator bindings.
-/
private def processForLoopDecrease (loopVar : String) (decrease : List Exp) : List Exp :=
  decrease.map (rewriteForLoopInvariant loopVar)

/--
  Collect all statements from a block and preceding blocks that form the for-loop preamble.
  This includes Range construction, into_iter call, and iterator setup.
-/
private partial def collectForLoopPreamble (stms : List Stm) :
    (List Stm × Option (List Stm × Stm)) :=
  -- Walk the statements looking for a Loop with isForLoop=true
  -- Return (pre-loop statements, Some (remaining, loop))
  let rec go (preAcc : List Stm) (rest : List Stm) :
      (List Stm × Option (List Stm × Stm)) :=
    match rest with
    | [] => (preAcc.reverse, none)
    | s :: tail =>
      match s with
      | .Loop true _ _ _ _ _ => (preAcc.reverse, some (tail, s))
      | .Block inner =>
        -- The loop might be nested inside blocks
        match findLoopInBlock inner with
        | some (innerPre, loopStm, innerPost) =>
          ((preAcc.reverse ++ innerPre), some (innerPost ++ tail, loopStm))
        | none => go (s :: preAcc) tail
      | _ => go (s :: preAcc) tail
  go [] stms
where
  findLoopInBlock (stms : List Stm) : Option (List Stm × Stm × List Stm) :=
    let rec goInner (pre : List Stm) (rest : List Stm) : Option (List Stm × Stm × List Stm) :=
      match rest with
      | [] => none
      | s :: tail =>
        match s with
        | .Loop true _ _ _ _ _ => some (pre.reverse, s, tail)
        | .Block inner =>
          match findLoopInBlock inner with
          | some (innerPre, loopStm, innerPost) =>
            some (pre.reverse ++ innerPre, loopStm, innerPost ++ tail)
          | none => goInner (s :: pre) tail
        | _ => goInner (s :: pre) tail
    goInner [] stms

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
  | .Assert (.Const (.Bool true)) => true
  | .AssertLean (.Const (.Bool true)) => true
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

private def specFnIsGeneric (f : SpecFn) : Bool :=
  let typTypeVarsOf : Typ → List String := fun _ => []  -- simplified; full version traverses
  !(f.inputs.flatMap (fun (_, ty) => typTypeVarsOf ty) ++
    typTypeVarsOf f.returnType).isEmpty

-- Simplified: just check for type params in signature
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

/-! ## Decrease/Return Artifact Stripping -/

private def isDecreaseArtifact : Stm → Bool
  | .Assign (.Var name) _ _ _ => name.startsWith "decrease"
  | .Call fn _ _ => toString fn |>.startsWith "CheckDecrease"
  | .Assert (.Call fn _ _) =>
    toString (CallFun.name fn) |>.startsWith "CheckDecrease"
  | .Assert (.Var name) => name.startsWith "CheckDecrease"
  | _ => false

private partial def stripDecreaseArtifacts : Stm → Stm
  | .Block stms =>
    .Block (stms.filter (!isDecreaseArtifact ·) |>.map stripDecreaseArtifacts)
  | .If cond b1 b2 =>
    .If cond (stripDecreaseArtifacts b1) (b2.map stripDecreaseArtifacts)
  | .DeadEnd stm => .DeadEnd (stripDecreaseArtifacts stm)
  | .Loop isFor label cond body invs dec =>
    .Loop isFor label cond (stripDecreaseArtifacts body) invs dec
  | stm => stm

private partial def hasReturnStm : Stm → Bool
  | .Return _ => true
  | .Block stms => stms.any hasReturnStm
  | .If _ b1 b2 => hasReturnStm b1 || (b2.map hasReturnStm |>.getD false)
  | .DeadEnd stm => hasReturnStm stm
  | _ => false

private def isAssumeFalse : Stm → Bool
  | .Assume (.Const (.Bool false)) => true
  | _ => false

private partial def blockHasReturn : List Stm → Bool
  | [] => false
  | (.Return _) :: _ => true
  | (.Block stms) :: rest => blockHasReturn stms || blockHasReturn rest
  | (.If _ b1 b2) :: rest =>
    hasReturnStm b1 || (b2.map hasReturnStm |>.getD false) || blockHasReturn rest
  | _ :: rest => blockHasReturn rest

private partial def stripReturnAssumeFalse : List Stm → List Stm
  | [] => []
  | (.Return e) :: rest =>
    .Return e :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
  | (.Block stms) :: rest =>
    let stripped := .Block (stripReturnAssumeFalse stms)
    if blockHasReturn stms then
      stripped :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
    else
      stripped :: stripReturnAssumeFalse rest
  | (.If cond b1 b2) :: rest =>
    let b1' := stripReturnDeep b1
    let b2' := b2.map stripReturnDeep
    let ifHasRet := hasReturnStm b1 || (b2.map hasReturnStm |>.getD false)
    let stripped := .If cond b1' b2'
    if ifHasRet then
      stripped :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
    else
      stripped :: stripReturnAssumeFalse rest
  | s :: rest => s :: stripReturnAssumeFalse rest
where
  stripReturnDeep : Stm → Stm
    | .Block stms => .Block (stripReturnAssumeFalse stms)
    | .If cond b1 b2 => .If cond (stripReturnDeep b1) (b2.map stripReturnDeep)
    | .DeadEnd stm => .DeadEnd (stripReturnDeep stm)
    | .Loop isFor label cond body invs dec =>
      .Loop isFor label cond (stripReturnDeep body) invs dec
    | s => s

private def collectDecreasesExps : Stm → List Exp
  | .Assign (.Var name) _ rhs _ =>
    if name.startsWith "decrease" then [rhs] else []
  | .Block stms => stms.flatMap collectDecreasesExps
  | _ => []

private def implicitLoopLabel (cond : Option (Stm × Exp)) (body : Stm) : String :=
  let seed := s!"{repr cond}|{repr body}"
  let h := seed.toList.foldl (fun acc c => (acc * 131 + c.toNat) % 1000000007) 0
  sanitizeIdent s!"loop_{h}"

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
  | .Const c => return constToBoole expected? c
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
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let ctor := Bld.fvar ctorIdx
    let args ← data.mapM (expToBoole env bound none)
    return Bld.appN ctor args
  | .Binary (.ExtEq deep ty) lhs rhs => do
    extEqExpToBoole env bound deep ty lhs rhs
  | .Binary (.Eq _) lhs rhs => do
    let (_, l, r) ← comparisonPrelude env bound lhs rhs
    return Bld.eq l r
  | .Binary .Ne lhs rhs => do
    let (_, l, r) ← comparisonPrelude env bound lhs rhs
    return Bld.neq l r
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
    | .Old => return Bld.old x
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
      let projIdx ← resolveFreeVar s!"Tuple_{size}_{field}"
      return Bld.app (Bld.fvar projIdx) x
    | _ =>
      match applyUnaryOp op x with
      | some result => return result
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToBoole env bound (some .Bool) c
    let t' ← expToBoole env bound expected? t
    let e' ← expToBoole env bound expected? e
    return Bld.ite c' t' e'
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
        addBoundVars (vars.map Prod.fst).toArray (reverse? := false)
        expToBoole env (vars.reverse ++ bound) (some .Bool) body
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      match q with
      | .Forall => return forallExpr binds body'
      | .Exists => return existsExpr binds body'
    | .Lambda vars => do
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray (reverse? := false)
        expToBoole env (vars.reverse ++ bound) none body
      -- Lambda is represented as a quantifier for now (like CoreToBoole)
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
  return Bld.eq lhs' rhs'

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
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let args ← (List.range size).mapM (fun i => do
      if i == field then pure rhs
      else do
        let projIdx ← resolveFreeVar s!"Tuple_{size}_{i}"
        pure (Bld.app (Bld.fvar projIdx) container))
    let updatedContainer := Bld.appN (Bld.fvar ctorIdx) args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer

/-! ## Statement Translation Main -/

mutual

partial def stmToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ)) :
    Stm → BuildM (List BStmt)
  | .Call fn _typArgs args => do
    if isGhostPervasiveCallName fn then
      return []
    let argsFiltered := normalizeCallArgsForCallee env fn args
    let callee := identToBoole fn
    let argsCore ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
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
    return [callStmt (mutOuts.toArray) callee (argsCore.toArray)]
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
      stmToBoole env projLayouts mutArgMap retVar? body
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
          return [setStmt (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else if isViewName fnName || isVecLenSpecName fnName || isVecLenExecName fnName
            || isVecIndexSpecName fnName || isVecIndexExecName fnName then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName => return [setStmt (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else
        let argsCore ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
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
          return [callStmt lhsNames callee argsCore.toArray]
        | none =>
          -- Projected l-value: use temporary
          let tmpName := sanitizeVarName s!"tmp_proj_call_{callee}"
          let ty' ← typToBooleType lhsTy
          let lhsNames := #[tmpName] ++ mutOuts.toArray
          let callS := callStmt lhsNames callee argsCore.toArray
          let tmpExpr ← resolveVar tmpName
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs tmpExpr
          return [varStmt tmpName ty', callS, setStmt (sanitizeVarName rootName) updatedRoot]
    | _ => do
      let rhs' ← expToBooleFlat env (some lhsTy) rhs
      match lvalueVarName? lhs with
      | some lhsName =>
        return [setStmt (sanitizeVarName lhsName) rhs']
      | none =>
        let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
        return [setStmt (sanitizeVarName rootName) updatedRoot]
  | .DeadEnd stm =>
    stmToBoole env projLayouts mutArgMap retVar? stm
  | .Return exp => do
    match exp, retVar? with
    | some e, some (retName, retTy) =>
      match e with
      | .EnumCtor _ "tuple%0" [] | .TupleCtor 0 [] | .StructCtor _ [] =>
        return [returnStmt none]
      | _ =>
        let rhs ← expToBooleFlat env (some retTy) e
        return [setStmt (sanitizeVarName retName) rhs, returnStmt none]
    | _, _ => return [returnStmt none]
  | .BreakOrContinue label isBreak =>
    match label with
    | some l => return [exitStmt (some (sanitizeIdent l))]
    | none =>
      throw s!"unsupported unlabeled {(if isBreak then "break" else "continue")} after loop normalization"
  | .If cond b1 b2 => do
    let c ← expToBooleFlat env (some .Bool) cond
    let thenStms ← stmToBoole env projLayouts mutArgMap retVar? b1
    let elseStms ← match b2 with
      | some s => stmToBoole env projLayouts mutArgMap retVar? s
      | none => pure []
    return [iteStmt c thenStms.toArray elseStms.toArray]
  | .Loop _isForLoop label cond body invs decrease => do
    -- For-loop recovery is handled in stmListToBooleAux; if we get here, emit while loop
    let (guardFromBody?, body') :=
      match extractLoopGuardFromBody body with
      | some (g, b') => (some g, b')
      | none => (none, body)
    let loopLabel? :=
      match label with
      | some l => some (sanitizeIdent l)
      | none =>
        let condNeeds := match cond with | some (s, _) => hasUnlabeledLoopControl s | none => false
        if condNeeds || hasUnlabeledLoopControl body' then
          some (implicitLoopLabel cond body)
        else
          none
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
    let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? bodyBound
    let loopStmt := whileStmt condExpr measureExpr? invExprs bodyStms.toArray
    let stmt := match loopLabel? with | some l => blockStmt l #[loopStmt] | none => loopStmt
    return [stmt]
  | .OpenInvariant stm =>
    stmToBoole env projLayouts mutArgMap retVar? stm
  | .ClosureInner body =>
    stmToBoole env projLayouts mutArgMap retVar? body
  | .Block stms =>
    stmListToBoole env projLayouts mutArgMap retVar? stms
  | .Reveal .. =>
    return []

/--
  Try to recover a for-loop from a list of statements containing a `Stm.Loop true`.
  Scans the statement list for:
  1. Pre-loop assignments that include a Range construction (start/end)
  2. A `Loop` with `isForLoop = true` whose body matches the iterator pattern
  If successful, emits a `forToStmt` and returns `some (emitted, remaining)`.
  Otherwise returns `none`.
-/
partial def tryForLoopRecovery (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (retVar? : Option (String × Typ))
    (stms : List Stm) : BuildM (Option (List BStmt × List Stm)) := do
  -- Find the first for-loop in the statement list
  match findForLoop [] stms with
  | none => pure none
  | some (preStms, loopStm, postStms) =>
    match loopStm with
    | .Loop true _label _cond body invs decrease =>
      match matchForLoopBody? body with
      | none => pure none
      | some info =>
        -- Find Range start/end from pre-loop context
        let allPreStms := flattenAllBlocks preStms
        match findRangeSetup? allPreStms with
        | none => pure none
        | some rangeInfo =>
          -- Successfully matched! Emit the for-loop.
          let processedInvs := processForLoopInvariants info.loopVarName invs
          let processedDecrease := processForLoopDecrease info.loopVarName decrease

          let loopVarTy ← typToBooleType info.loopVarTy
          let loopVarSan := sanitizeVarName info.loopVarName

          let startExpr ← expToBooleFlat env (some info.loopVarTy) rangeInfo.startExp
          let endE ← expToBooleFlat env (some info.loopVarTy) rangeInfo.endExp
          let limitExpr ← match bitWidthOfTyp info.loopVarTy with
            | some w => pure (bvSub w endE (bitvecConstNat w 1))
            | none => pure (intSub endE (intConst 1))

          -- Push the loop variable into scope for invariants, decreases, and body
          let (invExprs, measureExpr?, bodyStms) ← withScope do
            pushBoundVar loopVarSan
            let invExprs ← processedInvs.toArray.mapM (fun inv =>
              expToBooleFlat env (some .Bool) inv.body)
            let measureExpr? ← match processedDecrease with
              | [] => pure none
              | e :: _ => do
                let ce0 ← expToBooleFlat env none e
                let srcKind? := inferNumKind env [] e
                let ce ← coerceNumeric srcKind? (some .int) ce0
                pure (some ce)
            let userBodyStm := Stm.Block info.userBody
            let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? userBodyStm
            pure (invExprs, measureExpr?, bodyStms)

          let loopStmt := forToStmt loopVarSan loopVarTy startExpr limitExpr
            measureExpr? invExprs bodyStms.toArray

          -- Emit any non-scaffolding pre-loop statements, then the for-loop
          let preFiltered := allPreStms.filter fun
            | .Assign lhs _ _ _ =>
              match lvalueVarName? lhs with
              | some name => !isForLoopScaffoldingVar name && !name.startsWith "decrease"
              | none => true
            | .Call fn _ _ =>
              !(isIteratorNextName fn || isIntoIterName fn || isGhostPervasiveCallName fn)
            | _ => true
          let preBoole ← preFiltered.mapM (stmToBoole env projLayouts mutArgMap retVar?)
          pure (some (preBoole.flatten ++ [loopStmt], postStms))
    | _ => pure none
where
  findForLoop (pre : List Stm) (rest : List Stm) :
      Option (List Stm × Stm × List Stm) :=
    match rest with
    | [] => none
    | s :: tail =>
      match s with
      | .Loop true _ _ _ _ _ => some (pre.reverse, s, tail)
      | .Block inner =>
        -- Check if the loop is nested inside blocks
        match findForLoop [] (flattenAllBlocks [.Block inner]) with
        | some (innerPre, loopStm, innerPost) =>
          some (pre.reverse ++ innerPre, loopStm, innerPost ++ tail)
        | none => findForLoop (s :: pre) tail
      | _ => findForLoop (s :: pre) tail
  flattenAllBlocks (stms : List Stm) : List Stm :=
    stms.flatMap fun
      | .Block inner => flattenAllBlocks inner
      | s => [s]

partial def stmListToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ)) :
    List Stm → BuildM (List BStmt)
  | stms => do
    let normalized :=
      (flattenSeqBlocks (recoverComputeProofs (inlineTemps stms))).map stripSingletonBlocks
    -- Try for-loop recovery before normal processing
    let hasForLoop := normalized.any fun
      | .Loop true _ _ _ _ _ => true
      | _ => false
    if hasForLoop then
      match ← tryForLoopRecovery env projLayouts mutArgMap retVar? normalized with
      | some (forStms, postStms) =>
        let rest ← stmListToBooleAux env projLayouts mutArgMap retVar? postStms
        return forStms ++ rest
      | none =>
        stmListToBooleAux env projLayouts mutArgMap retVar? normalized
    else
      stmListToBooleAux env projLayouts mutArgMap retVar? normalized

partial def stmListToBooleAux (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ)) :
    List Stm → BuildM (List BStmt)
  | (.BreakOrContinue none true) :: (.Assume (.Const (.Bool false))) :: rest => do
    let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? rest
    return [assumeStmt "" (boolConst false)] ++ s2
  | a :: (.Assume e) :: next :: rest =>
    if isAssertAssumeEcho a e then
      stmListToBooleAux env projLayouts mutArgMap retVar? (a :: next :: rest)
    else if isTrivialTrueAssert a && isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
    else if isTrivialTrueAssert a then
      stmListToBooleAux env projLayouts mutArgMap retVar? ((.AssertCompute e) :: next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? a
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? ((.Assume e) :: next :: rest)
      return s1 ++ s2
  | (.Assume e) :: next :: rest =>
    if isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? (.Assume e)
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
      return s1 ++ s2
  | a :: next :: rest =>
    match next with
    | .Assume e =>
      if isAssertAssumeEcho a e then
        stmListToBooleAux env projLayouts mutArgMap retVar? (a :: rest)
      else if isTrivialTrueAssert a then
        stmListToBooleAux env projLayouts mutArgMap retVar? ((.AssertCompute e) :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
        return s1 ++ s2
    | _ =>
      if isTrivialTrueAssert a && isQueryStmt next then
        stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? (next :: rest)
        return s1 ++ s2
  | [stm] =>
    stmToBoole env projLayouts mutArgMap retVar? stm
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

def specFnToBoole (env : VarEnv) (emitBody : Bool) (f : SpecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let (inputBindings, inputNames) ← mkMonoInputs f.inputs
  let outputTy ← typToBooleType f.returnType
  let envLocal := extendEnv env f.inputs
  let (body?, specElts) ← withScope do
    addBoundVars inputNames (reverse? := false)
    let body? ← if emitBody then
      match f.body with
      | some b => pure (some (← expToBooleFlat envLocal (some f.returnType) b))
      | none => pure none
    else pure none
    let elts : Array (BooleDDM.SpecElt SourceRange) := #[]
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
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s)
  let setVars := match bodyStm? with | some body => collectSetVars body | none => []
  let bodyHasForLoop := match bodyStm? with | some body => stmHasForLoop body | none => false
  let inputNames := f.inputs.map Prod.fst
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let outputs := retDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan (reverse? := false)
    addBoundVars outputNamesSan (reverse? := false)
    let specElts ← mkSpecElts envLocal f.requires f.ensures []
    let localStmts ← localsToVarStmts localsAll
    let retVar? := if hasRet then some (f.retName, f.returnType) else none
    let bodyStmts ← match bodyStm? with
      | some stm => stmToBoole envLocal projLayouts mutArgMap retVar? stm
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
  let outputs := retDecls ++ mutOutputDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let isDeclOnly := match f.body with | .Block [] => true | _ => false
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan (reverse? := false)
    addBoundVars outputNamesSan (reverse? := false)
    let specElts ← mkSpecElts envLocal f.requires rewrittenEnsures []
    if isDeclOnly then
      let body := BooleDDM.Block.block default (ann #[])
      pure (specElts, body)
    else
      let localStmts ← localsToVarStmts localsAll
      -- Init mutable-out variables from inputs
      let mutOutInits ← mutOutDecls.mapM (fun (inName, outName, _payloadTy) => do
        let inExpr ← resolveVar inName
        pure (setStmt (sanitizeVarName outName) inExpr))
      let retVar? := if hasRet then some (f.retName, f.returnType) else none
      let bodyStmts ← stmToBoole envLocal projLayouts mutArgMap retVar? rewrittenBody
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
    addBoundVars inputNamesSan (reverse? := false)
    addBoundVars outputNamesSan (reverse? := false)
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
          addBoundVars inputNames (reverse? := false)
          let body ← match f.body with
            | some b => expToBooleFlat envLocal (some f.returnType) b
            | none => pure (boolConst true)
          let elts : Array (BooleDDM.SpecElt SourceRange) := #[]
          pure (body, elts)
        pure (BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy (ann specElts) body)
      pure [BooleDDM.Command.command_recfndefs default (ann recDecls)]
    -- Translate non-spec declarations normally
    let otherCmds ← others.foldlM (fun acc d => do
      let cmds ← declToBoole env projLayouts mutArgMap sfMap allDecls d
      return acc ++ cmds) []
    return recCmds ++ otherCmds

/-! ## Support Layer: Cast/Stub Declarations -/

private def mkCastFnDecl (name : String) (inputTy outputTy : Typ) : BuildM BCmd := do
  addFreeVars #[name]
  let nameAnn := ann name
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange := ann none
  let inputBinding := BooleDDM.Binding.mkBinding default (ann "x") (BooleDDM.TypeP.expr (← typToBooleType inputTy))
  let inputBindings := BooleDDM.Bindings.mkBindings default (ann #[inputBinding])
  let outputTy' ← typToBooleType outputTy
  pure (.command_fndecl default nameAnn typeArgs inputBindings outputTy')

private def mkAbstractTypeDecl (name : String) (params : List String) : BuildM BCmd := do
  addFreeVars #[name]
  let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    if params.isEmpty then ann none
    else
      let bindings := params.toArray.map fun p =>
        BooleDDM.Binding.mkBinding default (ann p) (BooleDDM.TypeP.type default)
      ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
  pure (.command_typedecl default (ann name) args)

private def mkAutoStubFnDecl (name : String) (arity : Nat) : BuildM BCmd := do
  addFreeVars #[name]
  let nameAnn := ann name
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange := ann none
  let bindings := (List.range arity).toArray.map (fun i =>
    BooleDDM.Binding.mkBinding default (ann s!"x{i}") (BooleDDM.TypeP.expr intTy))
  let inputBindings := BooleDDM.Bindings.mkBindings default (ann bindings)
  let outputTy := intTy
  pure (.command_fndecl default nameAnn typeArgs inputBindings outputTy)

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

/-- Main entry point: translate a list of VLIR declarations into BooleDDM commands. -/
private def isSupportCastName (name : String) : Bool :=
  isBvToIntCastName name || isBvToNatCastName name || isIntToBvCastName name ||
  isBvWidenCastName name || name == "nat_to_int" || name == "int_to_nat"

private def isSupportTypeName (name : String) : Bool :=
  name == "nat"

def declsToBooleProgram (decls : List Decl) :
    BuildM (Array BCmd) := do
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
  -- Collect free variable names referenced by translation
  let ctx ← get
  let referencedNames := ctx.allFreeVars
  -- Only emit support declarations for names actually referenced
  let mut supportCmds : Array BCmd := #[]
  if referencedNames.any (· == "nat") then
    supportCmds := supportCmds.push (← mkAbstractTypeDecl "nat" [])
  if referencedNames.any (· == "nat_to_int") then
    supportCmds := supportCmds.push (← mkCastFnDecl "nat_to_int" .Nat .Int)
  if referencedNames.any (· == "int_to_nat") then
    supportCmds := supportCmds.push (← mkCastFnDecl "int_to_nat" .Int .Nat)
  for w in supportedBvWidths do
    let castNames := [
      (bvToIntCastName w false, (.UInt w), Typ.Int),
      (bvToIntCastName w true, (.SInt w), Typ.Int),
      (bvToNatCastName w false, (.UInt w), Typ.Nat),
      (bvToNatCastName w true, (.SInt w), Typ.Nat),
      (intToBvCastName w false, Typ.Int, (.UInt w)),
      (intToBvCastName w true, Typ.Int, (.SInt w))]
    for (name, inTy, outTy) in castNames do
      if referencedNames.any (· == name) then
        supportCmds := supportCmds.push (← mkCastFnDecl name inTy outTy)
  for fromW in supportedBvWidths do
    for toW in supportedBvWidths do
      if fromW < toW then
        let uName := bvWidenCastName fromW toW false
        let sName := bvWidenCastName fromW toW true
        if referencedNames.any (· == uName) then
          supportCmds := supportCmds.push (← mkCastFnDecl uName (.UInt fromW) (.UInt toW))
        if referencedNames.any (· == sName) then
          supportCmds := supportCmds.push (← mkCastFnDecl sName (.SInt fromW) (.SInt toW))
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

end VerusLean
