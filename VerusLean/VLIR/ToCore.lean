/-
  VLIR to Strata Core Translation (WIP)

  Translates the Verus-Lean IR (VLIR) to Strata Core AST.
-/

import Std.Data.HashMap
import Strata.Languages.Core.Program
import Strata.Languages.Core.Factory
import Strata.DL.Lambda.LExpr
import VerusLean.VLIR.Defs

namespace VerusLean

namespace ToCore

open Core
open Lambda

-- Strata now uses `Unit` metadata for core identifiers/datatypes.
abbrev Visibility := Unit

namespace CoreIdent

-- Backward-compat constructor used throughout this file.
def unres (s : String) : CoreIdent := (s : CoreIdent)

end CoreIdent

abbrev CoreExpr := Core.Expression.Expr
abbrev VarEnv := Std.HashMap String Typ -- global/free variables
abbrev BoundEnv := List (String × Typ) -- bound variables introduced by binders in quantifiers, lets, etc.
structure MutArgInfo where
  idx : Nat
  ty : Typ

abbrev MutArgMap := Std.HashMap String (List MutArgInfo) -- Core callee name -> mutable argument metadata

/-! ## Utilities -/

-- Sanitize an identifier for Core emission:
-- first char: [A-Za-z_], rest chars: [A-Za-z0-9_'?!]
-- Characters outside this set are replaced by `_`.
def sanitizeIdent (s : String) : String :=
  match s.toList with
  | [] => "_"
  | c :: cs =>
    let first := if c.isAlpha || c == '_' then c else '_'
    let rest := cs.map (fun c =>
      if c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!' then c else '_')
    let out := String.ofList (first :: rest)
    -- `type` is a Core keyword in the concrete syntax.
    -- TODO: handle a full reserved-keyword set centrally.
    if out == "type" then "type_" else out

-- VLIR parser builds `Ident` from full crate + path segments,
-- here to Core symbols we drop one leading namespace/file segment
-- Examples:
--   `Datatypes.worthless_ctor`      -> `worthless_ctor`
--   `Datatypes::worthless::size`    -> `worthless::size`
--   `Datatypes_worthless_ctor`      -> `worthless_ctor`
-- TODO: projected-name collisions?
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

def isVecTypeName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "Vec" || s.endsWith "vec"

def usizeBitWidth : Nat := 64

def isSupportedBvWidth (w : Nat) : Bool :=
  w == 1 || w == 8 || w == 16 || w == 32 || w == 64

private def supportedBvWidths : List Nat := [1, 8, 16, 32, 64]

def vecLenName (base : String) : String :=
  s!"{base}_len"

def isVecLenSpecName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "spec_vec_len" || s.endsWith "Seq.len" || s.endsWith "seq.len"

-- Matches exec Vec length names like `alloc::vec::Vec::<T>::len`.
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

/-- Strata Core reserves these type names internally. We prefix Verus types
    that collide to avoid "reserved type name" errors. -/
private def strataReservedTypeNames : List String :=
  ["Seq", "Set", "Map", "Multiset", "Triggers", "TriggerGroup"]

/-- Verus stdlib collection types that we intentionally emit with their short
    conventional names in Core. This keeps generated output concise while still
    allowing user-defined `Set`/`Multiset` datatypes to be prefixed away from
    Strata/Core-reserved names. -/
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
  -- Keep a suffix to avoid collisions with the datatype type symbol (e.g. `point_ctor` vs `point`).
  datatypeNameOf dt ++ "_ctor"

def structCtorIdentOf (dt : Ident) : CoreIdent :=
  CoreIdent.unres (structCtorNameOf dt)

def enumCtorNameOf (dt : Ident) (variant : String) : String :=
  -- Keep datatype prefix to avoid collisions across enums that share variant names.
  datatypeNameOf dt ++ "_" ++ sanitizeIdent variant

def enumCtorIdentOf (dt : Ident) (variant : String) : CoreIdent :=
  CoreIdent.unres (enumCtorNameOf dt variant)

def fieldAccessorNameOf (field : String) : String :=
  match field.toNat? with
  | some i =>
    -- Tuple-style struct fields are serialized as `"0"`, `"1"`, ...
    -- Prefix with `_` so names stay legal and distinct (`_0`, `_1`, ...).
    s!"_{i}"
  | none =>
    sanitizeIdent field

def fieldAccessorIdentOf (field : String) : CoreIdent :=
  CoreIdent.unres (fieldAccessorNameOf field)

def datatypeDestructorNameOf (dt : Ident) (field : String) : String :=
  s!"{datatypeNameOf dt}..{fieldAccessorNameOf field}"

def datatypeDestructorIdentOf (dt : Ident) (field : String) : CoreIdent :=
  CoreIdent.unres (datatypeDestructorNameOf dt field)

def enumTesterNameOf (dt : Ident) (variant : String) : String :=
  let dtName := datatypeNameOf dt
  let ctorName := enumCtorNameOf dt variant
  s!"{dtName}..is{ctorName}"

def enumTesterIdentOf (dt : Ident) (variant : String) : CoreIdent :=
  CoreIdent.unres (enumTesterNameOf dt variant)

def projFieldNameOf (dt : Ident) (variant field : String) : String :=
  if field == "_" then
    -- Unnamed single-field variant projection: align with tuple-style selector
    -- naming emitted in `enumToCoreTypeDecl` (`..._{i}`), using slot 0.
    -- TODO: confirm current Verus JSON still emits `"field": "_"`; drop this
    -- case if exports consistently use numeric field names instead.
    s!"{datatypeNameOf dt}_{sanitizeIdent variant}_0"
  else
    match field.toNat? with
    | some i => s!"{datatypeNameOf dt}_{sanitizeIdent variant}_{i}"
    | none =>
      let dtName := datatypeNameOf dt
      let variantName := sanitizeIdent variant
      -- For enums, variant-qualified field selectors avoid duplicate names across
      -- constructors (e.g. Mammal.legs vs Arthropod.legs).
      if variantName.toLower == dtName.toLower then
        field
      else
        s!"{dtName}_{variantName}_{sanitizeIdent field}"

def declSentinelName : String := "__verus_decl__"

def declSentinel : CoreExpr :=
  LExpr.fvar () (CoreIdent.unres declSentinelName) none

def isDeclSentinel : CoreExpr → Bool
  | LExpr.fvar _ id _ => CoreIdent.toPretty id == declSentinelName
  | _ => false

def emptyStmtMeta : Imperative.MetaData Core.Expression := .empty

def mkInitStmt (name : CoreIdent) (ty : LTy) (rhs : CoreExpr) : Core.Statement :=
  Core.Statement.init name ty (some rhs) emptyStmtMeta

def mkSetStmt (name : CoreIdent) (rhs : CoreExpr) : Core.Statement :=
  Core.Statement.set name rhs emptyStmtMeta

def mkAssertStmt (label : String) (e : CoreExpr) : Core.Statement :=
  Core.Statement.assert label e emptyStmtMeta

def mkAssumeStmt (label : String) (e : CoreExpr) : Core.Statement :=
  Core.Statement.assume label e emptyStmtMeta

def mkCallStmt (lhs : List CoreIdent) (pname : String) (args : List CoreExpr) : Core.Statement :=
  Core.Statement.call lhs pname args emptyStmtMeta

-- Core now models labeled jumps as `exit <label>`.
def mkExitToLabelStmt (label : String) : Core.Statement :=
  Imperative.Stmt.exit (some label) emptyStmtMeta

/-- Emit a return statement.  Encoded as `assume [__return__]: false` which
    cuts off execution on this path (semantically correct for early return).
    The local pretty-printer merges `ret := expr; assume [__return__]: false`
    into `// return expr;`.  The official printer shows `assume false;` which
    is semantically honest.  Replace with native `return` when Strata adds
    support. -/
def mkReturnStmt : Core.Statement :=
  Core.Statement.assume "__return__" (LExpr.boolConst () false) emptyStmtMeta

def mkIteStmt (cond : CoreExpr) (thenb elseb : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.ite cond thenb elseb emptyStmtMeta

def mkBlockStmt (label : String) (body : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.block label body emptyStmtMeta

/-- True when a Core statement is `assume false` (but NOT a return or decreases sentinel). -/
private def isCoreAssumeFalse : Core.Statement → Bool
  | .cmd (.cmd (.assume label e _)) =>
    label != "__decreases__" && label != "__return__" && match e with
    | .const _ (.boolConst false) => true
    | _ => false
  | _ => false

/-- Strip `assume false` from Core statement lists, recursing into blocks/ite/loops. -/
private partial def stripCoreAssumeFalse : List Core.Statement → List Core.Statement
  | [] => []
  | s :: rest =>
    let s' := match s with
      | .block label body md => .block label (stripCoreAssumeFalse body) md
      | .ite cond tb eb md => .ite cond (stripCoreAssumeFalse tb) (stripCoreAssumeFalse eb) md
      | .loop g m invs body md => .loop g m invs (stripCoreAssumeFalse body) md
      | other => other
    if isCoreAssumeFalse s' then stripCoreAssumeFalse rest
    else s' :: stripCoreAssumeFalse rest

def identToCore (i : Ident) : CoreIdent :=
  CoreIdent.unres (sanitizeIdent (stripLeadingNamespace i.toString))

def sanitizeVarName (s : String) : String :=
  -- Preserve `%`-based temp numbering (`tmp%4`, `tmp%%1`, ...) to avoid
  -- collisions after sanitization.
  sanitizeIdent (s.replace "%" "_pct_")

def varToCore (s : String) : CoreIdent :=
  CoreIdent.unres (sanitizeVarName s)

def envFromDecls (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := (∅ : VarEnv)) (fun acc (n, t) => acc.insert n t)

def mutRefPayload? : Typ → Option Typ
  | .Decorated .MutRef ty => some ty
  | .Decorated _ ty => mutRefPayload? ty
  | _ => none

-- Track mutable-reference parameters by call-argument index (Core call sites are positional).
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

def boundIndex? (bound : BoundEnv) (name : String) : Option Nat :=
  let rec go (i : Nat) (rest : BoundEnv) : Option Nat :=
    match rest with
    | [] => none
    | (n, _) :: tail => if n == name then some i else go (i + 1) tail
  go 0 bound

def boundType? (bound : BoundEnv) (name : String) : Option Typ :=
  (bound.find? (fun (n, _) => n == name)).map Prod.snd

def isFuelVar : Exp → Bool
  | .Var name => name.startsWith "fuel%" || name.startsWith "fuel_"
  | _ => false

def normalizeCallArgs (args : List Exp) : List Exp :=
  -- Fuel vars are Verus-internal and not source-level arguments.
  args.filter (fun e => !isFuelVar e)

private def noParamMarkerKey (fname : String) : String :=
  s!"__verus_noparam_fn__{fname}"

private def addNoParamFnMarkers (env : VarEnv) (noParamFns : List String) : VarEnv :=
  noParamFns.foldl (init := env) (fun acc fname => acc.insert (noParamMarkerKey fname) .Bool)

private def hasNoParamFnMarker (env : VarEnv) (fname : String) : Bool :=
  env.contains (noParamMarkerKey fname)

/-- Key convention for storing spec function return types in `VarEnv`. -/
private def fnRetKey (fname : String) : String :=
  s!"__verus_fnret__{fname}"

/-- Use bare identifiers for translator-owned prelude helpers. -/
private def preludeIdent (name : String) : Ident :=
  .str .anonymous name

/-- Use a synthetic `vstd` namespace so `datatypeNameOf` canonicalizes the Seq
    prelude's public collection types to their short emitted names (`Seq`,
    `Set`) instead of reserving them as user datatypes. -/
private def preludeTypeIdent (name : String) : Ident :=
  .str (.str .anonymous "vstd") name

private def preludeStructTyp (name : String) (params : List Typ) : Typ :=
  .Struct (preludeTypeIdent name) params

private def seqPreludeTy (elem : Typ) : Typ :=
  preludeStructTyp "Seq" [elem]

private def setPreludeTy (elem : Typ) : Typ :=
  preludeStructTyp "Set" [elem]

/-- Type constructors owned by the optional Seq prelude snippet in
    `prelude/Seq.core.st`. The translator needs this list both to avoid
    placeholder auto-stubs when the prelude is present and to emit typed
    fallback declarations when it is absent. -/
private def seqPreludeOwnedTypeNames : List String :=
  ["Seq", "Set"]

/-- Type signatures for translator-owned prelude symbols that can appear in the
    emitted Core AST. This lets lowering treat the textual prelude as already
    loaded, and also lets translation fall back to typed stubs when the
    textual prelude file is unavailable. -/
private def knownPreludeFnSignature? (fname : String) : Option (List Typ × Typ) :=
  let t := Typ.TypParam "T"
  let a := Typ.TypParam "A"
  let b := Typ.TypParam "B"
  match fname with
  | "bv64_to_int_u" => some ([.UInt 64], .Int)
  | "bv64_to_nat_u" => some ([.UInt 64], .Nat)
  | "int_to_bv64_u" => some ([.Int], .UInt 64)
  | "Seq_len" => some ([seqPreludeTy t], .Nat)
  | "Seq_empty" => some ([], seqPreludeTy t)
  | "Seq_index" => some ([seqPreludeTy t, .Int], t)
  | "Seq_first" => some ([seqPreludeTy t], t)
  | "Seq_last" => some ([seqPreludeTy t], t)
  | "Seq_update" => some ([seqPreludeTy t, .Int, t], seqPreludeTy t)
  | "Seq_push" => some ([seqPreludeTy t, t], seqPreludeTy t)
  | "Seq_take" => some ([seqPreludeTy t, .Int], seqPreludeTy t)
  | "Seq_skip" => some ([seqPreludeTy t, .Int], seqPreludeTy t)
  | "Seq_add" => some ([seqPreludeTy t, seqPreludeTy t], seqPreludeTy t)
  | "Seq_subrange" => some ([seqPreludeTy t, .Int, .Int], seqPreludeTy t)
  | "Seq_new" => some ([.Nat, .SpecFn [.Int] t], seqPreludeTy t)
  | "Seq_lib_drop_last" => some ([seqPreludeTy t], seqPreludeTy t)
  | "Seq_lib_contains" => some ([seqPreludeTy t, t], .Bool)
  | "Seq_lib_remove" => some ([seqPreludeTy t, .Int], seqPreludeTy t)
  | "Seq_lib_filter" => some ([seqPreludeTy t, .SpecFn [t] .Bool], seqPreludeTy t)
  | "Seq_lib_map" => some ([seqPreludeTy a, .SpecFn [.Int, a] b], seqPreludeTy b)
  | "Seq_lib_map_values" => some ([seqPreludeTy a, .SpecFn [a] b], seqPreludeTy b)
  | "Seq_lib_sort_by" => some ([seqPreludeTy t, .SpecFn [t, t] .Bool], seqPreludeTy t)
  | "Seq_lib_to_set" => some ([seqPreludeTy t], setPreludeTy t)
  | "Set_finite" => some ([setPreludeTy t], .Bool)
  | "Vec_view" => some ([.Array t, .UInt 64], seqPreludeTy t)
  | _ => none

private def isPreludeOwnedTypeName (name : String) : Bool :=
  seqPreludeOwnedTypeNames.contains name

private def isPreludeOwnedValueName (name : String) : Bool :=
  (knownPreludeFnSignature? name).isSome

private def isSeqPreludeProvidedCastName : String → Bool
  | "bv64_to_int_u" | "bv64_to_nat_u" | "int_to_bv64_u" => true
  | _ => false

private def needsSeqPrelude (typeRefs opRefs : List String) : Bool :=
  typeRefs.any isPreludeOwnedTypeName ||
    opRefs.any (fun name => isPreludeOwnedValueName name && !isSeqPreludeProvidedCastName name)

/-- Look up the return type of a spec function stored in the `VarEnv`. -/
private def lookupFnRetType (env : VarEnv) (fname : String) : Option Typ :=
  env.get? (fnRetKey fname) <|> (knownPreludeFnSignature? fname).map Prod.snd

/-- Key convention for storing the i-th parameter type of a spec function. -/
private def fnParamKey (fname : String) (idx : Nat) : String :=
  s!"__verus_fnparam__{fname}__{idx}"

/-- Look up the i-th parameter type of a spec function. -/
private def lookupFnParamType (env : VarEnv) (fname : String) (idx : Nat) : Option Typ :=
  env.get? (fnParamKey fname idx) <|> do
    let (params, _) ← knownPreludeFnSignature? fname
    params.drop idx |>.head?

private def normalizeCallArgsForCallee (env : VarEnv) (fname : Ident) (args : List Exp) : List Exp :=
  let fnameStr := CoreIdent.toPretty (identToCore fname)
  let argsNoFuel := normalizeCallArgs args
  if hasNoParamFnMarker env fnameStr then
    -- Verus JSON can emit a fake argument at some call sites for zero-parameter
    -- functions (`no%param` shape), typically as boxed `0`.
    -- Strip this placeholder only for declarations that are actually zero-input
    -- in VLIR, so we do not accidentally rewrite real user arguments.
    argsNoFuel.filter (fun e =>
      match e with
      | .Unary (.Box .Int) (.Const (.Int 0)) => false
      | _ => true)
  else
    argsNoFuel

partial def vecVarFromExp : Exp → Option String
  | .Var x => some x
  | .Unary op e =>
    match op with
    | .Box _ | .Unbox _ | .Clip _ _ | .Old | .Trigger | .HasType _ => vecVarFromExp e
    | _ => none
  | .Call fn _ [arg] =>
    let name := CallFun.name fn
    if isViewName name then vecVarFromExp arg else none
  | _ => none

private partial def lvalueFromMutArgExp? : Exp → Option LValue
  | .Var name => some (.Var name)
  | .Unary op e =>
    match op with
    | .Proj dt variant field getVariant check =>
      (lvalueFromMutArgExp? e).map (fun base => .Proj base dt variant field getVariant check)
    | .Proj' size field =>
      (lvalueFromMutArgExp? e).map (fun base => .Proj' base size field)
    | .Box _ | .Unbox _ | .Clip _ _ | .Old | .Trigger | .HasType _ => lvalueFromMutArgExp? e
    | _ => none
  | .Call fn _ [arg] =>
    let name := CallFun.name fn
    if isViewName name then lvalueFromMutArgExp? arg else none
  | _ => none

private def projectedMutArgTmpName (callee : String) (idx : Nat) (arg : Exp) : String :=
  let seed := s!"{callee}_{idx}_{repr arg}"
  let h := seed.toList.foldl (fun acc c => acc * 131 + c.toNat) 0
  sanitizeIdent s!"tmp_mut_arg_{h}"

private structure MutArgProjectionRewrite where
  idx : Nat
  ty : Typ
  lhs : LValue
  tmp : String

private def collectMutArgProjectionRewrites (mutArgMap : MutArgMap) (callee : String)
    (args : List Exp) : Except String (List MutArgProjectionRewrite) := do
  let infos := (mutArgMap.get? callee).getD []
  let rec go (rest : List MutArgInfo) (acc : List MutArgProjectionRewrite) :
      Except String (List MutArgProjectionRewrite) := do
    match rest with
    | [] => pure acc.reverse
    | info :: tail =>
      let i := info.idx
      match (args.drop i).head? with
      | none =>
        throw s!"mutable call-arg index {i} out of bounds for {callee}"
      | some arg =>
        match vecVarFromExp arg with
        | some _ =>
          -- Plain variable mutable args can be passed directly as Core call outputs.
          go tail acc
        | none =>
          match lvalueFromMutArgExp? arg with
          | some lhs =>
            let rw : MutArgProjectionRewrite :=
              { idx := i, ty := info.ty, lhs := lhs, tmp := projectedMutArgTmpName callee i arg }
            go tail (rw :: acc)
          | none =>
            throw s!"mutable call arg must lower to a variable in {callee} at index {i}: {repr arg}"
  go infos []

private def replaceMutArgProjectionArgs (args : List Exp)
    (rewrites : List MutArgProjectionRewrite) : List Exp :=
  let tmpByIdx : Std.HashMap Nat String :=
    rewrites.foldl (init := (∅ : Std.HashMap Nat String)) (fun acc rw => acc.insert rw.idx rw.tmp)
  let rec go (i : Nat) : List Exp → List Exp
    | [] => []
    | arg :: rest =>
      let arg' := match tmpByIdx.get? i with | some tmp => .Var tmp | none => arg
      arg' :: go (i + 1) rest
  go 0 args

-- Compute Core call-output variables for mutable parameters after projection
-- rewrites have replaced non-variable l-values with temporary variables.
def mutCallOutputs (mutArgMap : MutArgMap) (callee : String) (args : List Exp) :
    Except String (List CoreIdent) := do
  let infos := (mutArgMap.get? callee).getD []
  infos.mapM (fun info =>
    let i := info.idx
    match (args.drop i).head? with
    | none =>
      throw s!"mutable call-arg index {i} out of bounds for {callee}"
    | some arg =>
      match vecVarFromExp arg with
      | some v => pure (varToCore v)
      | none =>
        throw s!"mutable call arg must lower to a variable in {callee} at index {i}: {repr arg}")

def isRangeTypeName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "range.range" || s.endsWith "range::range"

def isIteratorNextName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "next" && s.contains "iterator"

def isIntoIterName (name : Ident) : Bool :=
  let s := name.toString.toLower
  s.endsWith "into_iter" && s.contains "collect"

def rangeTypAndIndex? : Typ → Option (Ident × Typ)
  | .Struct n params =>
    if isRangeTypeName n then
      match params with
      | idx :: _ => some (n, idx)
      | [] => none
    else
      none
  | .Decorated _ ty => rangeTypAndIndex? ty
  | _ => none

def optionTypAndElem? : Typ → Option (Ident × Typ)
  | .Enum n params
  | .Struct n params =>
    match params with
    | elem :: _ => some (n, elem)
    | [] => none
  | .Decorated _ ty => optionTypAndElem? ty
  | _ => none

def rangeIndexTypFromExpected? : Option Typ → Option Typ
  | some (.Struct n params) =>
    if isRangeTypeName n then params.head? else none
  | some (.Decorated _ ty) => rangeIndexTypFromExpected? (some ty)
  | _ => none

def isRangeCtorFields (fields : List (String × Exp)) : Bool :=
  match fields with
  | [("start", _), ("end", _)] => true
  | _ => false

def firstStructParamFromExpected? : Option Typ → Option Typ
  | some (.Struct _ params) => params.head?
  | some (.Decorated _ ty) => firstStructParamFromExpected? (some ty)
  | _ => none

def isSeqTyp : Typ → Bool
  | .Struct name _ => datatypeNameOf name == "Seq"
  | .Decorated _ ty => isSeqTyp ty
  | _ => false

private def mkSeqLiteralExp (elems : List Exp) : Exp :=
  let seqEmpty : Exp := .Call (.Fun (preludeIdent "Seq_empty")) [] []
  elems.foldl (init := seqEmpty) (fun acc elem =>
    .Call (.Fun (preludeIdent "Seq_push")) [] [acc, elem])

/-! ## Type Translation -/

def monoTyOfTyp : Typ → LMonoTy
  | .Empty => .tcons "Unit" []
  | .Unit => .tcons "Unit" []
  | .Tuple t1 t2 => .tcons "Tuple" [monoTyOfTyp t1, monoTyOfTyp t2]
  | .Bool => .bool
  | .Int => .int
  -- Now we make `nat` a type in Core, but we will have a native `.nat` one day.
  | .Nat => .tcons "nat" []
  -- Strata Core currently has built-in bitvector operators only for 1/8/16/32/64.
  -- For other widths (e.g. 128), lower as `int` to keep translation total.
  | .UInt w
  | .SInt w => if isSupportedBvWidth w then .bitvec w else .int
  | .Char => .int -- TODO
  | .StrSlice => .string
  | .Array t => Core.mapTy .int (monoTyOfTyp t)
  | .TypParam name => .ftvar (sanitizeIdent name)
  | .SpecFn params ret =>
    let paramTys := params.map monoTyOfTyp
    LMonoTy.mkArrow' (monoTyOfTyp ret) paramTys
  | .Decorated _ ty => monoTyOfTyp ty -- TODO, ignore for now
  | .Struct name params =>
    if isVecTypeName name then
      match params with
      | t :: _ => Core.mapTy (.bitvec usizeBitWidth) (monoTyOfTyp t)
      | [] =>
        -- Unexpected: Vec without a type parameter. Use a placeholder element type
        -- so this shows up clearly in the generated Core program.
        Core.mapTy (.bitvec usizeBitWidth) (.tcons "MissingVecElem" [])
    else
      .tcons (datatypeNameOf name) (params.map monoTyOfTyp)
  | .Enum name params => .tcons (datatypeNameOf name) (params.map monoTyOfTyp)
  | .AirNamed str => .tcons str []

def bitWidthOfTyp : Typ → Option Nat
  | .UInt w
  | .SInt w => if isSupportedBvWidth w then some w else none
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

-- Evaluate a small arithmetic fragment that is often used for literal bounds
-- (e.g. `0 - 99`) so mixed int/bitvector comparisons can stay bit-precise.
private def constIntExprVal? : Exp → Option Int
  | .Const (.Int i) => some i
  | .Binary (.Arith .Add _) lhs rhs => do
    let l ← constIntExprVal? lhs
    let r ← constIntExprVal? rhs
    some (l + r)
  | .Binary (.Arith .Sub _) lhs rhs => do
    let l ← constIntExprVal? lhs
    let r ← constIntExprVal? rhs
    some (l - r)
  | .Binary (.Arith .Mul _) lhs rhs => do
    let l ← constIntExprVal? lhs
    let r ← constIntExprVal? rhs
    some (l * r)
  | _ => none

private def intFitsBitWidth (w : Nat) (signed : Bool) (i : Int) : Bool :=
  if signed then
    let lo : Int := -((2 : Int) ^ (w - 1))
    let hi : Int := (2 : Int) ^ (w - 1)
    lo <= i && i < hi
  else
    let hi : Int := (2 : Int) ^ w
    0 <= i && i < hi

-- Conservative check used by comparison typing:
-- can this expression be lowered at a target bitwidth without needing int-domain casts?
-- Today this intentionally only accepts integer constant fragments and branchy
-- combinations of such fragments (e.g. `if b then 17 else 2`).
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

-- Choose a common bitvector type for a comparison predicate (Eq/Ne/Inequality).
-- Returns `none` when the comparison must fall back to the integer domain
-- (e.g. one side is a bitvector and the other a non-representable integer).
def chooseBitArgTyForCmp
    (lhs rhs : Exp) (lhsInfo? rhsInfo? : Option (Nat × Bool)) : Option Typ :=
  match lhsInfo?, rhsInfo? with
  | some i1, some i2 =>
    -- Prefer same-signed width-promotion over int fallback when possible,
    -- so mixed-width bitvector comparisons avoid `bv*_to_int_*` casts.
    (chooseBitPromotionInfo? i1 i2).map (fun (w, signed) => bitTypOfInfo w signed)
  | some (w, s), none =>
    -- If needed, promote the BV side to a larger supported width so an integer
    -- literal expression can be represented directly in BV (avoids bv->int).
    (choosePromotedWidthForExpr? w s rhs).map (fun w' => bitTypOfInfo w' s)
  | none, some (w, s) =>
    -- Symmetric literal-expression widening for left-side non-BV terms.
    (choosePromotedWidthForExpr? w s lhs).map (fun w' => bitTypOfInfo w' s)
  | none, none => none

def bvToIntCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_int_s" else s!"bv{w}_to_int_u"

def bvToNatCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_nat_s" else s!"bv{w}_to_nat_u"

def isBvToIntCastName (s : String) : Bool :=
  s.endsWith "_to_int_u" || s.endsWith "_to_int_s"

def isBvToNatCastName (s : String) : Bool :=
  s.endsWith "_to_nat_u" || s.endsWith "_to_nat_s"

/-- Wrap a bitvector expression in a coercion cast to the target type when needed.
    Returns `none` if no coercion is needed (types match or can't determine). -/
def mkCoercionCast (argInfo? : Option (Nat × Bool)) (targetTy : Typ) (e : CoreExpr) : Option CoreExpr :=
  match argInfo? with
  | some (w, signed) =>
    match targetTy with
    | .Int =>
      -- bv → int: use bv*_to_int_*
      some (LExpr.mkApp () (LExpr.op () (CoreIdent.unres (bvToIntCastName w signed)) none) [e])
    | .Nat =>
      -- bv → nat: use bv*_to_nat_*
      some (LExpr.mkApp () (LExpr.op () (CoreIdent.unres (bvToNatCastName w signed)) none) [e])
    | _ => none
  | none => none

def bvToIntCastOp (w : Nat) (signed : Bool) : CoreExpr :=
  LExpr.op () (CoreIdent.unres (bvToIntCastName w signed)) none

def isBvToIntCastExpr : CoreExpr → Bool
  | .app _ (.op _ id _) _ => isBvToIntCastName (CoreIdent.toPretty id)
  | _ => false

-- Wrap a bitvector expression in a `bv*_to_int_*` cast when it is a known
-- bitvector type but the comparison/context expects an integer.
-- Avoids double-wrapping expressions that are already cast.
def castExprToIntIfBitInfo (info? : Option (Nat × Bool)) (e : CoreExpr) : CoreExpr :=
  match info? with
  | some (w, signed) =>
    if isBvToIntCastExpr e then
      e
    else
      LExpr.mkApp () (bvToIntCastOp w signed) [e]
  | none => e

def bvWidenCastName (fromW toW : Nat) (signed : Bool) : String :=
  if signed then s!"bv{fromW}_to_bv{toW}_s" else s!"bv{fromW}_to_bv{toW}_u"

def isBvWidenCastName (s : String) : Bool :=
  -- Match the structured form `bv<N>_to_bv<M>_<u|s>` generated by `bvWidenCastName`.
  (s.startsWith "bv" && (s.find? "_to_bv").isSome && (s.endsWith "_u" || s.endsWith "_s"))

private def bvWidenCastOp (fromW toW : Nat) (signed : Bool) : CoreExpr :=
  LExpr.op () (CoreIdent.unres (bvWidenCastName fromW toW signed)) none

private def castExprToWiderBv (fromW toW : Nat) (signed : Bool) (e : CoreExpr) : CoreExpr :=
  if fromW == toW then
    e
  else
    LExpr.mkApp () (bvWidenCastOp fromW toW signed) [e]

private def widenCastTargetWidth? (name : String) : Option Nat :=
  match name.splitOn "_to_bv" with
  | [_from, rest] =>
    let digits := String.ofList <| rest.toList.takeWhile (fun c => c.isDigit)
    if digits.isEmpty then none else digits.toNat?
  | _ => none

private def appHeadOpName? : CoreExpr → Option String
  | .op _ id _ => some (CoreIdent.toPretty id)
  | .app _ fn _ => appHeadOpName? fn
  | _ => none

-- Check whether a Core expression already operates at a given bitvector width,
-- by inspecting the head operator name (e.g. `Bv32.Add`, `bv16_to_bv32_u`).
-- Used to avoid inserting redundant width-promotion casts.
private def exprLooksLikeBitWidth (w : Nat) : CoreExpr → Bool
  | e =>
    match appHeadOpName? e with
    | some s =>
      let bvPrefix := s!"Bv{w}."
      s.startsWith bvPrefix || widenCastTargetWidth? s == some w
    | none => false

-- Insert a bv-to-bv widening cast when the source and target are the same
-- signedness but differ in width. Returns the expression unchanged when source
-- already matches the target, or throws when the cast is not representable
-- (e.g. mismatched signedness).
private def castExprToBitInfoIfNeeded
    (srcInfo? targetInfo? : Option (Nat × Bool)) (e : CoreExpr) :
    Except String CoreExpr := do
  match srcInfo?, targetInfo? with
  | some (sw, ss), some (tw, ts) =>
    if sw == tw && ss == ts then
      pure e
    else if ss == ts && canPromoteBvWidths sw tw then
      if exprLooksLikeBitWidth tw e then
        pure e
      else
        pure <| castExprToWiderBv sw tw ss e
    else
      throw s!"unsupported bitvector cast from ({sw}, signed={ss}) to ({tw}, signed={ts})"
  | _, _ => pure e

def vecElemTyp? : Typ → Option Typ
  | .Struct name params =>
    if isVecTypeName name then
      match params with
      | t :: _ => some t
      | [] => none
    else
      none
  | .Decorated _ ty => vecElemTyp? ty
  | _ => none

-- Core has no dedicated Vec primitive yet. Encode each Vec local as
-- the index -> element map + `*_len : bv64`.
def expandVecDecls (decls : List (String × Typ)) : List (String × Typ) :=
  decls.flatMap (fun (n, t) =>
    match vecElemTyp? t with
    | some _ => [(n, t), (vecLenName n, Typ.UInt usizeBitWidth)]
    | none => [(n, t)])

/-! ## Expression Translation -/

def constToCore (expected? : Option Typ) : Const → CoreExpr
  | .Bool b => LExpr.boolConst () b
  | .Int i =>
    match expected?.bind bitWidthOfTyp with
    | some w =>
      LExpr.bitvecConst () w (BitVec.ofInt w i)
    | none => LExpr.intConst () i
  | .StrSlice s => LExpr.strConst () s
  | .Char c => LExpr.intConst () c.toNat

def bvByWidth (w : Nat)
    (op1 op8 op16 op32 op64 : CoreExpr) : Option CoreExpr :=
  match w with
  | 1 => some op1
  | 8 => some op8
  | 16 => some op16
  | 32 => some op32
  | 64 => some op64
  | _ => none

def bvOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "And" => bvByWidth w Core.bv1AndOp Core.bv8AndOp Core.bv16AndOp Core.bv32AndOp Core.bv64AndOp
  | "Or" => bvByWidth w Core.bv1OrOp Core.bv8OrOp Core.bv16OrOp Core.bv32OrOp Core.bv64OrOp
  | "Xor" => bvByWidth w Core.bv1XorOp Core.bv8XorOp Core.bv16XorOp Core.bv32XorOp Core.bv64XorOp
  | "Shl" => bvByWidth w Core.bv1ShlOp Core.bv8ShlOp Core.bv16ShlOp Core.bv32ShlOp Core.bv64ShlOp
  | "UShr" => bvByWidth w Core.bv1UShrOp Core.bv8UShrOp Core.bv16UShrOp Core.bv32UShrOp Core.bv64UShrOp
  | "SShr" => bvByWidth w Core.bv1SShrOp Core.bv8SShrOp Core.bv16SShrOp Core.bv32SShrOp Core.bv64SShrOp
  | "Not" => bvByWidth w Core.bv1NotOp Core.bv8NotOp Core.bv16NotOp Core.bv32NotOp Core.bv64NotOp
  | _ => none

def bvArithOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "Add" => bvByWidth w Core.bv1AddOp Core.bv8AddOp Core.bv16AddOp Core.bv32AddOp Core.bv64AddOp
  | "Sub" => bvByWidth w Core.bv1SubOp Core.bv8SubOp Core.bv16SubOp Core.bv32SubOp Core.bv64SubOp
  | "Mul" => bvByWidth w Core.bv1MulOp Core.bv8MulOp Core.bv16MulOp Core.bv32MulOp Core.bv64MulOp
  | "UDiv" => bvByWidth w Core.bv1UDivOp Core.bv8UDivOp Core.bv16UDivOp Core.bv32UDivOp Core.bv64UDivOp
  | "UMod" => bvByWidth w Core.bv1UModOp Core.bv8UModOp Core.bv16UModOp Core.bv32UModOp Core.bv64UModOp
  | "SDiv" => bvByWidth w Core.bv1SDivOp Core.bv8SDivOp Core.bv16SDivOp Core.bv32SDivOp Core.bv64SDivOp
  | "SMod" => bvByWidth w Core.bv1SModOp Core.bv8SModOp Core.bv16SModOp Core.bv32SModOp Core.bv64SModOp
  | _ => none

def bvCmpOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "ULt" => bvByWidth w Core.bv1ULtOp Core.bv8ULtOp Core.bv16ULtOp Core.bv32ULtOp Core.bv64ULtOp
  | "ULe" => bvByWidth w Core.bv1ULeOp Core.bv8ULeOp Core.bv16ULeOp Core.bv32ULeOp Core.bv64ULeOp
  | "UGt" => bvByWidth w Core.bv1UGtOp Core.bv8UGtOp Core.bv16UGtOp Core.bv32UGtOp Core.bv64UGtOp
  | "UGe" => bvByWidth w Core.bv1UGeOp Core.bv8UGeOp Core.bv16UGeOp Core.bv32UGeOp Core.bv64UGeOp
  | "SLt" => bvByWidth w Core.bv1SLtOp Core.bv8SLtOp Core.bv16SLtOp Core.bv32SLtOp Core.bv64SLtOp
  | "SLe" => bvByWidth w Core.bv1SLeOp Core.bv8SLeOp Core.bv16SLeOp Core.bv32SLeOp Core.bv64SLeOp
  | "SGt" => bvByWidth w Core.bv1SGtOp Core.bv8SGtOp Core.bv16SGtOp Core.bv32SGtOp Core.bv64SGtOp
  | "SGe" => bvByWidth w Core.bv1SGeOp Core.bv8SGeOp Core.bv16SGeOp Core.bv32SGeOp Core.bv64SGeOp
  | _ => none

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
  if !used.contains base then
    base
  else
    let rec go : List Nat → String
      | [] => s!"{base}_fresh"
      | i :: rest =>
        let cand := s!"{base}_{i}"
        if used.contains cand then go rest else cand
    go (List.range (used.length + 1))

def binaryOpToCore : BinaryOp → Option CoreExpr
  | .And => some Core.boolAndOp
  | .Or => some Core.boolOrOp
  | .Implies => some Core.boolImpliesOp
  | .Eq _ => none
  | .Ne => none
  | .Xor => none
  | .Inequality .Le => some Core.intLeOp
  | .Inequality .Lt => some Core.intLtOp
  | .Inequality .Ge => some Core.intGeOp
  | .Inequality .Gt => some Core.intGtOp
  | .Arith .Add _ => some Core.intAddOp
  | .Arith .Sub _ => some Core.intSubOp
  | .Arith .Mul _ => some Core.intMulOp
  | .Arith .EuclideanDiv _ => some Core.intDivOp
  | .Arith .EuclideanMod _ => some Core.intModOp
  | .Bitwise _ _ => none

def unaryOpToCore : UnaryOp → Option CoreExpr
  | .Not => some Core.boolNotOp
  | _ => none

-- Infer bitwidth/signedness so numeric ops can stay bit-precise in Core.
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
      -- Look up the spec function's return type so that function-call results
      -- are correctly recognized as bitvectors (avoids spurious bv→int casts
      -- in comparisons like `mul(d, k) == v`).
      let fnStr := CoreIdent.toPretty (identToCore name)
      (lookupFnRetType env fnStr).bind bitInfoOfTyp
  | .Unary (.BitNot (some w)) e =>
    inferBitInfo env bound e <|>
      (if isSupportedBvWidth w then some (w, false) else none)
  -- `Unbox(T, e)` carries the concrete result type of a polymorphic call.
  -- Use the annotation so comparisons involving generic results are emitted
  -- with the correct bitvector type (e.g. `Unbox(U8, g(u))` → width 8).
  -- Fall through to the inner expression when the annotation is non-BV
  -- (e.g. `Unbox(Int, Var(x))` in quantifier bodies still checks `x`).
  | .Unary (.Unbox t) e => bitInfoOfTyp t <|> inferBitInfo env bound e
  -- `Box(T, e)` wraps a value of type T for polymorphism.
  -- Same logic as Unbox: use annotation, fall through if non-BV.
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

-- Inline let-bindings since Core expressions are let-free.
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
  -- Preserve pre-state references (`old`) across name substitutions.
  | .Unary .Old e => .Unary .Old e
  | .Unary op e => .Unary op (substExp name rhs e)
  | .Binary op e1 e2 => .Binary op (substExp name rhs e1) (substExp name rhs e2)
  | .If c t f => .If (substExp name rhs c) (substExp name rhs t) (substExp name rhs f)
  | .Bind bind body =>
    match bind with
    | .Let v ty e =>
      let e' := substExp name rhs e
      if v == name then
        .Bind (.Let v ty e') body
      else
        let rhsRefs := expVarRefs rhs
        if rhsRefs.contains v then
          let v' := freshenedName v (rhsRefs ++ expVarRefs body ++ [name])
          let bodyRenamed := substExp v (.Var v') body
          .Bind (.Let v' ty e') (substExp name rhs bodyRenamed)
        else
          .Bind (.Let v ty e') (substExp name rhs body)
    | .Quant q vars trigs =>
      -- Trigger exprs reference the quantifier's own bound variables, so they
      -- are unaffected by substitution of external names.
      if vars.any (fun (v, _) => v == name) then
        .Bind (.Quant q vars trigs) body
      else
        .Bind (.Quant q vars trigs) (substExp name rhs body)
    | .Lambda vars =>
      if vars.any (fun (v, _) => v == name) then
        .Bind (.Lambda vars) body
      else
        .Bind (.Lambda vars) (substExp name rhs body)
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (substExp name rhs))
  | .MatchBlock scrut body =>
    let (e, t) := scrut
    .MatchBlock (substExp name rhs e, t) (substExp name rhs body)

def substExps (subs : List (String × Exp)) (e : Exp) : Exp :=
  subs.foldl (fun acc (n, rhs) => substExp n rhs acc) e

/-! ### Trigger LExpr encoding

We encode quantifier trigger groups into the `trigger` slot of `LExpr.quant`
using Strata's official trigger ops from `Core.Factory`:

  • empty trigger list  → `LExpr.noTrigger ()` (= `bvar 0`)
  • non-empty           → `Core.mkTriggerExpr groups`

which builds an `Triggers.addGroup` / `TriggerGroup.addTrigger` tree that
Strata's pretty-printer and verifier natively understand.
-/

mutual

-- Shared setup for Eq/Ne/Inequality lowering:
-- Infer bitvector context for both sides, choose a common comparison type via
-- width-promotion, and insert casts as needed.
-- When no common bv type is possible (e.g. bv vs. int), falls back to int domain.
private partial def comparisonPreludeToCore
    (env : VarEnv) (bound : BoundEnv) (lhs rhs : Exp) :
    Except String (Option Typ × CoreExpr × CoreExpr) := do
  let lhsInfo? := inferBitInfo env bound lhs
  let rhsInfo? := inferBitInfo env bound rhs
  let argTy? := chooseBitArgTyForCmp lhs rhs lhsInfo? rhsInfo?
  let mixedIntMode := argTy?.isNone && (lhsInfo?.isSome || rhsInfo?.isSome)
  let sideTy? := if mixedIntMode then some Typ.Int else argTy?
  let targetInfo? := argTy?.bind bitInfoOfTyp
  let l0 ← expToCoreWithBound env bound sideTy? lhs
  let r0 ← expToCoreWithBound env bound sideTy? rhs
  let l ←
    if mixedIntMode then
      pure (castExprToIntIfBitInfo lhsInfo? l0)
    else
      castExprToBitInfoIfNeeded lhsInfo? targetInfo? l0
  let r ←
    if mixedIntMode then
      pure (castExprToIntIfBitInfo rhsInfo? r0)
    else
      castExprToBitInfoIfNeeded rhsInfo? targetInfo? r0
  return (argTy?, l, r)

-- Translate each trigger Exp into a CoreExpr and encode the groups into a
-- single LExpr tree suitable for the trigger slot of LExpr.quant.
partial def mkTriggersLExpr (env : VarEnv) (boundVars : BoundEnv)
    (trigs : List (List Exp)) : Except String CoreExpr := do
  if trigs.isEmpty then
    return LExpr.noTrigger ()
  let groups ← trigs.mapM (fun group =>
    group.mapM (fun e => expToCoreWithBound env boundVars none e))
  return Core.mkTriggerExpr groups

partial def expToCoreWithBound (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) :
    Exp → Except String CoreExpr
  | .Var x =>
    let actualTy? := boundType? bound x <|> env.get? x
    let asInt := expected?.map isIntTyp |>.getD false
    match boundIndex? bound x with
    | some idx =>
      let e := LExpr.bvar () idx
      if asInt then
        return castExprToIntIfBitInfo (actualTy?.bind bitInfoOfTyp) e
      else
        return e
    | none =>
      let ty? := actualTy?.map monoTyOfTyp
      let e := LExpr.fvar () (varToCore x) ty?
      if asInt then
        return castExprToIntIfBitInfo (actualTy?.bind bitInfoOfTyp) e
      else
        return e
  | .Const c => return constToCore expected? c
  | .StructCtor dt fields => do
    let ctor := LExpr.op () (structCtorIdentOf dt) none
    -- For `Range { start, end }`, propagate the expected index type so
    -- numeric literals (e.g. `1`) are emitted at the same width/sign as `end`.
    let fieldExpected? :=
      if isRangeTypeName dt || isRangeCtorFields fields then
        rangeIndexTypFromExpected? expected? <|> firstStructParamFromExpected? expected?
      else
        none
    let args ← fields.mapM (fun (_, e) => expToCoreWithBound env bound fieldExpected? e)
    return LExpr.mkApp () ctor args
  | .EnumCtor dt variant data => do
    let ctor := LExpr.op () (enumCtorIdentOf dt variant) none
    let args ← data.mapM (fun (_, e) => expToCoreWithBound env bound none e)
    return LExpr.mkApp () ctor args
  | .TupleCtor size data => do
    let ctor := LExpr.op () (CoreIdent.unres s!"Tuple_ctor_{size}") none
    let args ← data.mapM (expToCoreWithBound env bound none)
    return LExpr.mkApp () ctor args
  | .Binary (.Eq _) lhs rhs => do
    let (_, l, r) ← comparisonPreludeToCore env bound lhs rhs
    return LExpr.eq () l r
  | .Binary .Ne lhs rhs => do
    let (_, l, r) ← comparisonPreludeToCore env bound lhs rhs
    let eq := LExpr.eq () l r
    return LExpr.mkApp () Core.boolNotOp [eq]
  | .Binary .Xor lhs rhs => do
    -- Boolean XOR = !(a ↔ b). No BV inference needed (operands are always Bool).
    let l ← expToCoreWithBound env bound none lhs
    let r ← expToCoreWithBound env bound none rhs
    let eq := LExpr.mkApp () Core.boolEquivOp [l, r]
    return LExpr.mkApp () Core.boolNotOp [eq]
  | .Binary (.Inequality cmp) lhs rhs => do
    let (argTy?, l, r) ← comparisonPreludeToCore env bound lhs rhs
    match argTy? with
    | some ty =>
      match bitInfoOfTyp ty with
      | some (w, signed) =>
        let opName := match cmp with
          | .Le => if signed then "SLe" else "ULe"
          | .Lt => if signed then "SLt" else "ULt"
          | .Ge => if signed then "SGe" else "UGe"
          | .Gt => if signed then "SGt" else "UGt"
        match bvCmpOp w opName with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        throw s!"internal error: expected bitvector comparison type, got {repr ty}"
    | none =>
      match binaryOpToCore (.Inequality cmp) with
      | some bop => return LExpr.mkApp () bop [l, r]
      | none => throw s!"unsupported inequality op: {repr cmp}"
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
        if bs == es && canPromoteBvWidths bw ew then
          some (ew, es)
        else
          some (bw, bs)
      | some b, none => some b
      | none, some e =>
        -- Avoid forcing a signedness from context when both BV operands were
        -- already known but had conflicting signedness.
        if hasMixedSignedBitArgs then none else some e
      | none, none => none
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    let l0 ← expToCoreWithBound env bound argTy? lhs
    let r0 ← expToCoreWithBound env bound argTy? rhs
    let l ← castExprToBitInfoIfNeeded lhsInfo? info? l0
    let r ← castExprToBitInfoIfNeeded rhsInfo? info? r0
    match op with
    | .Bitwise bitop _ =>
      let w? := match bitop with
        | .Shl w _
        | .Shr w => some w
        | _ => info?.map Prod.fst
      let signed := info?.map Prod.snd |>.getD false
      let opName := match bitop with
        | .BitAnd => "And"
        | .BitOr => "Or"
        | .BitXor => "Xor"
        | .Shl _ _ => "Shl"
        | .Shr _ => if signed then "SShr" else "UShr"
      let resolvedW := w?.getD usizeBitWidth
      match bvOp resolvedW opName with
      | some bop => return LExpr.mkApp () bop [l, r]
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
        match bvArithOp w opName with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        match binaryOpToCore op with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported binary op: {repr op}"
    | _ =>
      match binaryOpToCore op with
      | some bop => return LExpr.mkApp () bop [l, r]
      | none => throw s!"unsupported binary op: {repr op}"
  | .Unary op e => do
    let x ←
      match op with
      | .Clip (.U w) _ =>
        let targetW := w.toNat
        -- When widening (inner width < target), translate the inner
        -- expression at its natural width first, then widen.  This
        -- preserves source structure: e.g. `(x ^ y) as u64` stays as
        -- "XOR then widen" instead of becoming "widen then XOR" which
        -- would look identical to `(x as u64) ^ (y as u64)`.
        -- For non-widening cases or expressions without a known inner
        -- width (e.g. literals), propagate the target so constToCore
        -- picks the right BV width.
        let innerInfo? := inferBitInfo env bound e
        let isWidening := match innerInfo? with
          | some (iw, _) => decide (iw < targetW) | none => false
        let hint? := if isWidening then
          innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
        else
          some (.UInt targetW)
        let x0 ← expToCoreWithBound env bound hint? e
        if isSupportedBvWidth targetW then
          castExprToBitInfoIfNeeded innerInfo? (some (targetW, false)) x0
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
        let x0 ← expToCoreWithBound env bound hint? e
        if isSupportedBvWidth targetW then
          castExprToBitInfoIfNeeded innerInfo? (some (targetW, true)) x0
        else
          pure x0
      | .Clip .Nat _ =>
        expToCoreWithBound env bound (some .Nat) e
      -- Box(T, e): translate the inner expression with T as the expected
      -- type, so e.g. `Box(U64, Const(Int, 10))` produces `bv{64}(10)`
      -- instead of an untyped int literal.
      | .Box t => expToCoreWithBound env bound (some t) e
      | _ => expToCoreWithBound env bound expected? e
    match op with
    | .Clip _ _ => return x
    | .BitNot w? =>
      -- Resolve target bit-info: prefer expected type, then inferred operand
      -- type, then the annotation width (if present) as final fallback.
      let srcInfo? := inferBitInfo env bound e
      let annotFallback := w?.bind (fun w0 =>
        if isSupportedBvWidth w0 then some (w0, false) else none)
      let targetInfo? := expected?.bind bitInfoOfTyp <|> srcInfo? <|> annotFallback
      match targetInfo?.map Prod.fst with
      | some w =>
        let x' ← castExprToBitInfoIfNeeded srcInfo? targetInfo? x
        match bvOp w "Not" with
        | some bop => return LExpr.mkApp () bop [x']
        | none => throw s!"unsupported bitvector width {w} for op Not"
      | none => throw "missing bitvector width for op Not"
    | .Old => return x
    | .Trigger => return x
    | .Box _ => return x
    | .Unbox _ => return x
    | .HasType _ => return x
    | .Proj dt variant field _getVariant check =>
      -- `getVariant` is mode-check metadata in Verus (spec-vs-exec); it does not
      -- change the semantic field value, so Core lowering uses the same
      -- destructor form in both cases.
      --
      -- `check = Yes` carries an extra proof obligation in Verus (`is_variant`
      -- before projection). We currently do not have an expression-local way to
      -- emit that assertion in Core without changing control flow.
      -- Fail explicitly instead of silently dropping the check.
      if check == .Yes then
        throw s!"unsupported checked field projection: {dt}::{variant}.{field}"
      let projField := projFieldNameOf dt variant field
      let proj := LExpr.op () (datatypeDestructorIdentOf dt projField) none
      return LExpr.mkApp () proj [x]
    | .IsVariant dt variant =>
      let isFn := LExpr.op () (enumTesterIdentOf dt variant) none
      return LExpr.mkApp () isFn [x]
    | .Proj' size field =>
      let proj := LExpr.op () (CoreIdent.unres s!"Tuple_{size}_{field}") none
      return LExpr.mkApp () proj [x]
    | _ =>
      match unaryOpToCore op with
      | some uop => return LExpr.mkApp () uop [x]
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToCoreWithBound env bound (some .Bool) c
    let t' ← expToCoreWithBound env bound expected? t
    let e' ← expToCoreWithBound env bound expected? e
    return LExpr.ite () c' t' e'
  | .Call fn _typs args => do
    let fname := CallFun.name fn
    let argsFiltered := normalizeCallArgsForCallee env fname args
    let mkFallback := do
      let fnStr := CoreIdent.toPretty (identToCore fname)
      -- Translate arguments with per-parameter expected types when available.
      let args' ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
        -- Look up the declared parameter type for this position.
        let paramTy? := lookupFnParamType env fnStr idx
        let argExpected? := paramTy? <|> (match expected? with
          | some ty => if isIntTyp ty then some Typ.Int else none
          | none => none)
        let argExpr ← expToCoreWithBound env bound argExpected? arg
        -- Insert coercion if the argument is a bitvector but the parameter
        -- expects `nat` or `int` (widening cast that Verus erases).
        let argInfo? := inferBitInfo env bound arg
        match paramTy? with
        | some paramTy =>
          match mkCoercionCast argInfo? paramTy argExpr with
          | some coerced => pure coerced
          | none => pure argExpr
        | none => pure argExpr)
      let f := LExpr.op () (identToCore fname) none
      return LExpr.mkApp () f args'
    if isViewName fname then
      match argsFiltered with
      | [arg] =>
        match vecVarFromExp arg with
        | some base =>
          match env.get? base |>.bind vecElemTyp? with
          | some _ =>
            let vecExpr ← expToCoreWithBound env bound none arg
            let lenName := vecLenName base
            let lenTy? : Option LMonoTy := env.get? lenName |>.map monoTyOfTyp
            let lenExpr : CoreExpr := LExpr.fvar () (varToCore lenName) lenTy?
            return LExpr.mkApp () (LExpr.op () (CoreIdent.unres "Vec_view") none) [vecExpr, lenExpr]
          | none =>
            expToCoreWithBound env bound expected? arg
        | none =>
          expToCoreWithBound env bound expected? arg
      | _ => mkFallback
    else if isVecLenSpecName fname || isVecLenExecName fname then
      match argsFiltered with
      | [arg] =>
        match vecVarFromExp arg with
        | some base =>
          let isVec := env.get? base |>.bind vecElemTyp? |>.isSome
          if isVec then
            let lenVar := vecLenName base
            let ty? := env.get? lenVar |>.map monoTyOfTyp
            return LExpr.fvar () (varToCore lenVar) ty?
          else
            mkFallback
        | none => mkFallback
      | _ => mkFallback
    else if isVecIndexSpecName fname || isVecIndexExecName fname then
      match argsFiltered with
      | [vArg, iArg] =>
        match vecVarFromExp vArg with
        | some base =>
          if (env.get? base |>.bind vecElemTyp? |>.isSome) then
            let vecSource :=
              match vArg with
              | .Call fn _ [arg] =>
                if isViewName (CallFun.name fn) then arg else vArg
              | _ => vArg
            let v ← expToCoreWithBound env bound none vecSource
            let i ← expToCoreWithBound env bound (some (Typ.UInt usizeBitWidth)) iArg
            return LExpr.mkApp () Core.mapSelectOp [v, i]
          else
            mkFallback
        | none =>
          mkFallback
      | _ => mkFallback
    else
      mkFallback
  | .CallLambda body args => do
    let fnExpr ← expToCoreWithBound env bound none body
    let args' ← args.mapM (expToCoreWithBound env bound none)
    return LExpr.mkApp () fnExpr args'
  | .Bind bind body =>
    match bind with
    | .Let v ty rhs =>
      let rhs' :=
        match rhs with
        | .ArrayLiteral elems =>
          if isSeqTyp ty then mkSeqLiteralExp elems else rhs
        | _ => rhs
      let body' := substExp v rhs' body
      expToCoreWithBound env bound expected? body'
    | .Quant q vars trigs => do
      let bitInfo? := inferBitInfo env bound body
      let vars' :=
        match bitInfo? with
        | some (w, signed) =>
          vars.map (fun (p : String × Typ) =>
            let n := p.fst
            let ty := p.snd
            match ty with
            | .Int | .Nat =>
              if signed then (n, Typ.SInt w) else (n, Typ.UInt w)
            | _ => (n, ty))
        | none => vars
      let boundVars := vars'.reverse ++ bound
      let bodyExpr ← expToCoreWithBound env boundVars (some .Bool) body
      -- Translate trigger groups into CoreExpr and encode for the trigger slot.
      let trigExpr ← mkTriggersLExpr env boundVars trigs
      let qk := match q with
        | .Forall => Lambda.QuantifierKind.all
        | .Exists => Lambda.QuantifierKind.exist
      -- Attach triggers to the innermost quantifier (last in `vars'`); outer
      -- ones get `noTrigger`.  Strata's grammar expects trigger groups on a
      -- single `forallT`/`existsT`, and `collectQuantChain` in the pretty-
      -- printer will flatten the nested quants back into one multi-binder form.
      let n := vars'.length
      let indexed := (List.range n).zip vars'
      let wrap := fun ((i : Nat), (v, ty)) acc =>
        let trig := if i == n - 1 then trigExpr else LExpr.noTrigger ()
        LExpr.quant () qk (sanitizeVarName v) (some (monoTyOfTyp ty)) trig acc
      return indexed.foldr wrap bodyExpr
    | .Lambda vars => do
      let boundVars := vars.reverse ++ bound
      let bodyExpr ← expToCoreWithBound env boundVars none body
      let wrap := fun (v, ty) acc => LExpr.abs () (sanitizeVarName v) (some (monoTyOfTyp ty)) acc
      return vars.foldr wrap bodyExpr
  | .MatchBlock _scrut body =>
    expToCoreWithBound env bound expected? body
  | .ArrayLiteral elems => do
    let elemExpected? :=
      if expected?.map isSeqTyp |>.getD false then
        firstStructParamFromExpected? expected?
      else
        none
    let args ← elems.mapM (expToCoreWithBound env bound elemExpected?)
    if expected?.map isSeqTyp |>.getD false then
      -- Lower `seq![a, b, c]` to the Seq API when the surrounding type
      -- already tells us this literal is a Verus sequence.
      let seqEmpty := LExpr.op () (CoreIdent.unres "Seq_empty") none
      let seqPush := LExpr.op () (CoreIdent.unres "Seq_push") none
      return args.foldl (init := seqEmpty) (fun acc arg =>
        LExpr.mkApp () seqPush [acc, arg])
    else
      let lit := LExpr.op () (CoreIdent.unres s!"Array_literal_{elems.length}") none
      return LExpr.mkApp () lit args

end

abbrev expToCore (env : VarEnv) (expected? : Option Typ) (e : Exp) :
    Except String CoreExpr :=
  expToCoreWithBound env [] expected? e

/-! ## Temporary Inlining -/

-- Temporarily inline tmp% assignments (from Verus lowering) into subsequent statements.
-- Loop-guard extraction now recognizes `if !cond { break; }` so we inline inside loops too
def isTempName (s : String) : Bool :=
  if s.startsWith "tmp" then
    let tail := s.drop 3
    !tail.isEmpty && tail.all Char.isDigit
  else
    false

def lvalueVarName? : LValue → Option String
  | .Var s => some s
  | _ => none

-- Procedure-call destinations in Core must be plain variables.
-- For projected destinations (`x.f := call ...`), use a deterministic
-- temporary call output and then rebuild/update the projected root.
private def projectedCallTmpName (fn : String) (lhs : LValue) : String :=
  let seed := s!"{fn}_{repr lhs}"
  let h := seed.toList.foldl (fun acc c => acc * 131 + c.toNat) 0
  sanitizeIdent s!"tmp_proj_call_{h}"

private structure ProjLayout where
  -- Rebuild metadata for `base.field := rhs` lowering:
  -- constructor symbol + constructor-field order for one datatype variant.
  dt : Ident
  variant : String
  ctor : CoreIdent
  fields : List String
  isEnum : Bool

private def projLayoutsFromDecl : Decl → List ProjLayout
  | .struct s =>
    [{ dt := s.name
       variant := datatypeNameOf s.name
       ctor := structCtorIdentOf s.name
       fields := s.fields.map Prod.fst
       isEnum := false }]
  | .enum e =>
    e.fields.map (fun field =>
      match field with
      | .labeled variant data =>
        { dt := e.name
          variant := variant
          ctor := enumCtorIdentOf e.name variant
          fields := data.map (fun (fname, _) => projFieldNameOf e.name variant fname)
          isEnum := true }
      | .tuple variant ts =>
        { dt := e.name
          variant := variant
          ctor := enumCtorIdentOf e.name variant
          fields := (List.range ts.length).map (fun i => projFieldNameOf e.name variant (toString i))
          isEnum := true })
  | .mutualBlock ds =>
    ds.flatMap projLayoutsFromDecl
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
    ([field,
      sanitizeIdent field,
      projFieldNameOf dt variant field,
      projFieldNameOf dt (datatypeNameOf dt) field]).eraseDups
  candidates.find? (fun c => layout.fields.contains c)

private def lvalueToExp : LValue → Exp
  | .Var name => .Var name
  | .Proj base dt variant field getVariant check =>
    .Unary (.Proj dt variant field getVariant check) (lvalueToExp base)
  | .Proj' base size field =>
    .Unary (.Proj' size field) (lvalueToExp base)

private def lvalueReadExprToCore (env : VarEnv) (lv : LValue) : Except String CoreExpr :=
  expToCore env none (lvalueToExp lv)

private def updateProjContainerExpr
    (container : CoreExpr) (layout : ProjLayout) (dt : Ident)
    (targetField : String) (updatedField : CoreExpr) :
    Except String CoreExpr := do
  if !layout.fields.contains targetField then
    throw s!"projection field `{targetField}` not found in datatype `{datatypeNameOf dt}` variant `{layout.variant}`"
  let args := layout.fields.map (fun fieldName =>
    if fieldName == targetField then
      updatedField
    else
      let proj := LExpr.op () (datatypeDestructorIdentOf dt fieldName) none
      LExpr.mkApp () proj [container])
  let ctor := LExpr.op () layout.ctor none
  return LExpr.mkApp () ctor args

private def updateTupleContainerExpr
    (container : CoreExpr) (size field : Nat) (updatedField : CoreExpr) :
    Except String CoreExpr := do
  if field >= size then
    throw s!"tuple projection index `{field}` out of bounds for tuple size `{size}`"
  let args := (List.range size).map (fun i =>
    if i == field then
      updatedField
    else
      let proj := LExpr.op () (CoreIdent.unres s!"Tuple_{size}_{i}") none
      LExpr.mkApp () proj [container])
  let ctor := LExpr.op () (CoreIdent.unres s!"Tuple_ctor_{size}") none
  return LExpr.mkApp () ctor args

private partial def lowerProjectedAssignRhsToRoot
    (env : VarEnv) (projLayouts : List ProjLayout) :
    LValue → CoreExpr → Except String (String × CoreExpr)
  -- Bubble an update from the innermost projected destination to the root variable:
  --   x.a.b := v
  -- becomes
  --   x := x with a := (x.a with b := v)
  | .Var name, rhs => pure (name, rhs)
  | .Proj base dt variant field _getVariant check, rhs => do
    if check == .Yes then
      throw s!"unsupported checked projection assignment destination: {dt}::{variant}.{field}"
    let container ← lvalueReadExprToCore env base
    let some layout := findProjLayout? projLayouts dt variant
      | throw s!"missing projection layout for assignment destination `{dt}::{variant}.{field}`"
    let some targetField := resolveProjFieldName? layout dt variant field
      | throw s!"could not resolve projection field `{field}` in `{dt}::{variant}`"
    let updatedContainer ← updateProjContainerExpr container layout dt targetField rhs
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer
  | .Proj' base size field, rhs => do
    let container ← lvalueReadExprToCore env base
    let updatedContainer ← updateTupleContainerExpr container size field rhs
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer

private def mutArgProjectionBridgeStmts (env : VarEnv) (projLayouts : List ProjLayout)
    (rewrites : List MutArgProjectionRewrite) :
    Except String (List Core.Statement × List Core.Statement) := do
  let pre ← rewrites.mapM (fun rw => do
    let rhs ← lvalueReadExprToCore env rw.lhs
    pure <| mkInitStmt (varToCore rw.tmp) (.forAll [] (monoTyOfTyp rw.ty)) rhs)
  let post ← rewrites.mapM (fun rw => do
    let tmpExpr := LExpr.fvar () (varToCore rw.tmp) (some (monoTyOfTyp rw.ty))
    let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts rw.lhs tmpExpr
    pure <| mkSetStmt (varToCore rootName) updatedRoot)
  pure (pre, post)

private structure LoweredMutCallArgs where
  argsFiltered : List Exp
  argsCore : List CoreExpr
  mutOuts : List CoreIdent
  pre : List Core.Statement
  post : List Core.Statement

private def lowerMutCallArgs (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (callee : String) (argsFiltered : List Exp) :
    Except String LoweredMutCallArgs := do
  -- For projected mutable arguments (e.g. `x.f`), bridge through temporaries:
  --   pre: read projection into tmp
  --   call: pass tmp as mutable out
  --   post: write tmp back into the projected root.
  let rewrites ← collectMutArgProjectionRewrites mutArgMap callee argsFiltered
  let argsFiltered' := replaceMutArgProjectionArgs argsFiltered rewrites
  let argsCore ← argsFiltered'.zipIdx.mapM (fun (arg, idx) => do
    let paramTy? := lookupFnParamType env callee idx
    let argExpr ← expToCore env none arg
    let argInfo? := inferBitInfo env [] arg
    match paramTy? with
    | some paramTy =>
      match mkCoercionCast argInfo? paramTy argExpr with
      | some coerced => pure coerced
      | none => pure argExpr
    | none => pure argExpr)
  let mutOuts ← mutCallOutputs mutArgMap callee argsFiltered'
  let (pre, post) ← mutArgProjectionBridgeStmts env projLayouts rewrites
  pure { argsFiltered := argsFiltered', argsCore := argsCore, mutOuts := mutOuts, pre := pre, post := post }

partial def stripSingletonBlocks : Stm → Stm
  | .Block [s] => stripSingletonBlocks s
  | s => s

-- In statement-sequence contexts, plain `Block` wrappers are sequencing noise.
-- Flattening them lets sequence-sensitive rewrites match across these wrappers.
partial def flattenSeqBlocks : List Stm → List Stm
  | [] => []
  | (.Block stms) :: rest => flattenSeqBlocks stms ++ flattenSeqBlocks rest
  | s :: rest => s :: flattenSeqBlocks rest

-- Calls that lower to side-effect-free Core expressions and are safe to inline
-- when cleaning up temporary-prefix assignments.
private def isPureBuiltinCallExp : Exp → Bool
  | .Call fn _ _ =>
    let fn := CallFun.name fn
    isViewName fn || isVecLenSpecName fn || isVecLenExecName fn
      || isVecIndexSpecName fn || isVecIndexExecName fn
  | _ => false

def tempAssignFromPrefix : Stm → Option (String × Exp)
  -- Collect temp assignments like `tmp1 := e`.
  -- Only block inlining when `rhs` is a top-level `.Call` that needs
  -- statement-level lowering (e.g. for mut-arg handling).  Nested calls
  -- inside other expression forms (Binary, Unary, …) always translate as
  -- pure function applications via `expToCore`, so they are safe to inline.
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
  -- Loop-guard prefixes are extracted from source guard expressions.
  -- Here we allow call RHSs because they come from guard evaluation and must
  -- be substituted back into the recovered guard (e.g., `tmp := f(...); if !p(tmp) break`).
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name =>
        if isTempName name then some (name, rhs) else none
      | none => none
    | _ => none

def dropCondTempAssignFromPrefix : Stm → Option String
  -- After guard substitution, drop only temp-prefix assignments that are known
  -- to lower to pure Core expressions (no statement-level side effects).
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
  -- In `cond = some (prefixStm, guardExpr)`, `prefixStm` may define temps via
  -- init assignments, and `guardExpr` can reference those temps.
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

def extractLoopGuardFromBody : Stm → Option (Exp × Stm)
  -- Recognize lowered loop heads used when `loop_isolation(false)`:
  --   Loop.cond = none
  --   body      = [tmp-prefix]* ; if (!guard) { break; } ; tail
  --
  -- This recovers `(guard, tail)` from the body prefix.
  --
  -- Recognize lowered loop heads:
  --   [tmp_i := rhs_i]* ; if (!guard) { break; } ; tail
  -- and recover source-style guard/body by substituting the temporary bindings.
  -- `rhs_i` may include calls (e.g., `tmp := Vec_len(v)`), so this path uses
  -- `splitGuardTempPrefix` rather than the call-free temp inliner split.
  -- TODO: continue-based guards, non-empty else branches,
  -- and guard checks that are not the first non-temp statement.
  | .Block stms =>
    -- Newer Verus SST can wrap the guard-temp prefix in an extra sequence-only
    -- `Block` node. Flatten those wrappers so the prefix matcher still sees:
    --   [tmp-prefix]* ; if (!guard) { break; } ; tail
    let linear := (flattenSeqBlocks stms).map stripSingletonBlocks
    let (subs, rest) := splitGuardTempPrefix linear
    match rest with
    | s :: tail =>
      match breakGuardFromPrefix s with
      | some guard => some (substExps subs guard, Stm.Block tail)
      | none => none
    | [] => none
  | _ => none

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

private def renameLValueVar (src dst : String) : LValue → LValue
  | .Var name =>
    if name == src then .Var dst else .Var name
  | .Proj base dt variant field getVariant check =>
    .Proj (renameLValueVar src dst base) dt variant field getVariant check
  | .Proj' base size field =>
    .Proj' (renameLValueVar src dst base) size field

partial def renameStmVar (src dst : String) : Stm → Stm
  | .Call fn typs args => .Call fn typs (args.map (substExp src (.Var dst)))
  | .Assert e => .Assert (substExp src (.Var dst) e)
  | .AssertBitVector reqs ens =>
    .AssertBitVector (reqs.map (substExp src (.Var dst))) (ens.map (substExp src (.Var dst)))
  | .AssertQuery mode body => .AssertQuery mode (renameStmVar src dst body)
  | .AssertCompute e => .AssertCompute (substExp src (.Var dst) e)
  | .AssertLean e => .AssertLean (substExp src (.Var dst) e)
  | .Assume e => .Assume (substExp src (.Var dst) e)
  | .Assign lhs lhsTy e lhsIsInit =>
    .Assign (renameLValueVar src dst lhs) lhsTy (substExp src (.Var dst) e) lhsIsInit
  | .DeadEnd stm => .DeadEnd (renameStmVar src dst stm)
  | .Return e => .Return (e.map (substExp src (.Var dst)))
  | .BreakOrContinue label isBreak => .BreakOrContinue label isBreak
  | .If cond b1 b2 =>
    .If (substExp src (.Var dst) cond) (renameStmVar src dst b1) (b2.map (renameStmVar src dst))
  | .Loop isFor label cond body invs decrease =>
    let cond' := cond.map (fun (s, e) => (renameStmVar src dst s, substExp src (.Var dst) e))
    let invs' := invs.map (fun inv => { inv with body := substExp src (.Var dst) inv.body })
    let decrease' := decrease.map (substExp src (.Var dst))
    .Loop isFor label cond' (renameStmVar src dst body) invs' decrease'
  | .OpenInvariant stm => .OpenInvariant (renameStmVar src dst stm)
  | .ClosureInner body => .ClosureInner (renameStmVar src dst body)
  | .Block stms => .Block (stms.map (renameStmVar src dst))
  | .Reveal fn fuel => .Reveal fn fuel

def applyNameSubstsExp (subs : List (String × String)) (e : Exp) : Exp :=
  subs.foldl (fun acc (src, dst) => substExp src (.Var dst) acc) e

def applyNameSubstsStm (subs : List (String × String)) (s : Stm) : Stm :=
  subs.foldl (fun acc (src, dst) => renameStmVar src dst acc) s

private partial def expMentionsVar (target : String) : Exp → Bool
  | .Var x => x == target
  | .Call _ _ args =>
    args.any (expMentionsVar target)
  | .CallLambda body args =>
    expMentionsVar target body || args.any (expMentionsVar target)
  | .StructCtor _ fields =>
    fields.any (fun (_, e) => expMentionsVar target e)
  | .EnumCtor _ _ fields =>
    fields.any (fun (_, e) => expMentionsVar target e)
  | .TupleCtor _ elems =>
    elems.any (expMentionsVar target)
  | .Unary _ e =>
    expMentionsVar target e
  | .Binary _ e1 e2 =>
    expMentionsVar target e1 || expMentionsVar target e2
  | .If c t f =>
    expMentionsVar target c || expMentionsVar target t || expMentionsVar target f
  | .Bind (.Let _ _ e) body =>
    expMentionsVar target e || expMentionsVar target body
  | .Bind (.Quant _ _ _) body =>
    expMentionsVar target body
  | .Bind (.Lambda _) body =>
    expMentionsVar target body
  | .ArrayLiteral elems =>
    elems.any (expMentionsVar target)
  | .MatchBlock (scrut, _) body =>
    expMentionsVar target scrut || expMentionsVar target body
  | .Const _ => false

private partial def lvalueMentionsVar (target : String) : LValue → Bool
  | .Var name => name == target
  | .Proj base _ _ _ _ _ => lvalueMentionsVar target base
  | .Proj' base _ _ => lvalueMentionsVar target base

private partial def stmMentionsVar (target : String) : Stm → Bool
  | .Call _ _ args =>
    args.any (expMentionsVar target)
  | .Assert e
  | .AssertCompute e
  | .AssertLean e
  | .Assume e =>
    expMentionsVar target e
  | .AssertBitVector reqs enss =>
    reqs.any (expMentionsVar target) || enss.any (expMentionsVar target)
  | .AssertQuery _ body =>
    stmMentionsVar target body
  | .Assign lhs _ rhs _ =>
    lvalueMentionsVar target lhs || expMentionsVar target rhs
  | .DeadEnd s
  | .OpenInvariant s
  | .ClosureInner s =>
    stmMentionsVar target s
  | .Reveal .. => false
  | .Return e? =>
    e?.map (expMentionsVar target) |>.getD false
  | .BreakOrContinue _ _ => false
  | .If cond b1 b2 =>
    expMentionsVar target cond ||
      stmMentionsVar target b1 ||
      (b2.map (stmMentionsVar target)).getD false
  | .Loop _ _ cond body invs decrease =>
    let condMentions :=
      match cond with
      | some (s, e) => stmMentionsVar target s || expMentionsVar target e
      | none => false
    let invMentions := invs.any (fun inv => expMentionsVar target inv.body)
    let decMentions := decrease.any (expMentionsVar target)
    condMentions || invMentions || decMentions || stmMentionsVar target body
  | .Block stms =>
    stms.any (stmMentionsVar target)

mutual
partial def inlineTempsInStm : Stm → Stm
  | .AssertQuery mode body => .AssertQuery mode (inlineTempsInStm body)
  | .DeadEnd stm => .DeadEnd (inlineTempsInStm stm)
  | .If cond b1 b2 =>
    -- Conservatively keep branch bodies unchanged.
    -- Sequence-local temp inlining can drop branch-local temp chains that feed
    -- values used after the `if`, causing non-faithful translation.
    .If cond b1 b2
  | .Loop isFor label cond body invs decrease =>
    -- Keep `prefixStm` (the first component of `cond`) intact so loop lowering
    -- can substitute its temp assignments into `guardExpr`.
    let cond' := cond
    let body' :=
      match body with
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
    -- Drop temp assignment only when this sequence actually consumes the temp.
    -- If not consumed in the remaining statements, keep the assignment to
    -- preserve cross-block uses (e.g. branch-local temp assigned then used
    -- after the `if` at outer scope).
    | some (lhs, rhs) =>
      if rest'.any (stmMentionsVar lhs) then
        rest'.map (substStm lhs rhs)
      else
        inlineTempsInStm stm :: rest'
    | none => inlineTempsInStm stm :: rest'
end

/-! ## Statement Translation -/

def mkLoop (guard : CoreExpr) (measure : Option CoreExpr) (invs : List CoreExpr)
    (body : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.loop guard measure invs body emptyStmtMeta

private def dropTempPrefixCoreAssigns (dropVars : List String) :
    List Core.Statement → List Core.Statement :=
  if dropVars.isEmpty then
    id
  else
    List.filter (fun s =>
      match s with
      | .cmd (.cmd (.init name _ _ _)) => !(dropVars.contains (CoreIdent.toPretty name))
      | .cmd (.cmd (.set name _ _)) => !(dropVars.contains (CoreIdent.toPretty name))
      | _ => true)

def loopInvariantToCore (env : VarEnv) (invs : List LoopInvariant) :
    Except String (List CoreExpr) := do
  invs.mapM (fun inv => expToCore env (some .Bool) inv.body)

def andExprs (es : List CoreExpr) : CoreExpr :=
  match es with
  | [] => LExpr.boolConst () true
  | e :: rest => rest.foldl (init := e) (fun acc x => LExpr.mkApp () Core.boolAndOp [acc, x])

def dropTrueConjuncts (es : List CoreExpr) : List CoreExpr :=
  es.filter (fun e =>
    match e with
    | .boolConst _ true => false
    | _ => true)

def mkQueryObligationExpr (reqs ensures : List CoreExpr) : CoreExpr :=
  -- Avoid vacuous forms like `true ==> ...` in emitted query obligations.
  let reqs' := dropTrueConjuncts reqs
  let ensures' := dropTrueConjuncts ensures
  match reqs' with
  | [] => andExprs ensures'
  | _ => LExpr.mkApp () Core.boolImpliesOp [andExprs reqs', andExprs ensures']

def assertQueryModeLabel : AssertQueryMode → String
  | .NonLinear => "nonlinear_query"
  | .BitVector => "bitvector_query"
  | .Other _ => "assert_query"

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
  | (.Assert e) :: rest
  | (.AssertLean e) :: rest =>
    let (ens, tail) := takeLeadingEnsuresRev rest
    (e :: ens, tail)
  | stms => ([], stms)

-- Verus lowers `assert ... by (...)` query bodies to a shape with
-- leading assumptions (query requires) and trailing assertions (query ensures).
-- We recover that boundary here and encode the query as one implication goal.
def queryReqEnsFromBody (body : Stm) : Option (List Exp × List Exp) :=
  let stms := (queryBodyStms body).map stripSingletonBlocks
  let (reqs, rest) := takeLeadingAssumes stms
  let (ensRev, _) := takeLeadingEnsuresRev rest.reverse
  let ens := ensRev.reverse
  if ens.isEmpty then none else some (reqs, ens)

-- Structural equality on VLIR expressions, used to detect Verus lowering
-- patterns (assert-assume echoes, query scaffolding assumes).
def sameExpShape (e₁ e₂ : Exp) : Bool := e₁ == e₂

-- Verus query lowering can place `assume ensure_i` right before the query node.
-- Keeping that assume would make the query obligation vacuous in Core.
def isQueryScaffoldingAssume (assumed : Exp) : Stm → Bool
  | .AssertBitVector _ ensures =>
    ensures.any (fun e => sameExpShape e assumed)
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

def isGhostPervasiveCallName (fn : Ident) : Bool :=
  let s := fn.toString.toLower
  s.contains "pervasive" && s.contains "ghost_"

def shouldDropAssignAsForLoopScaffolding (lhs : LValue) : Bool :=
  match lvalueVarName? lhs with
  | some name =>
    name.startsWith "VERUS_ghost_" ||
    name == "VERUS_loop_result"
  | none => false

def shouldDropForLoopScaffoldingLocal (name : String) : Bool :=
  name.startsWith "VERUS_ghost_" || name == "VERUS_loop_result"

private def implicitLoopLabel (cond : Option (Stm × Exp)) (body : Stm) : String :=
  let seed := s!"{repr cond}|{repr body}"
  -- Keep synthetic labels deterministic but compact for readability.
  let h := seed.toList.foldl (fun acc c => (acc * 131 + c.toNat) % 1000000007) 0
  sanitizeIdent s!"loop_{h}"

private partial def hasUnlabeledLoopControl : Stm → Bool
  -- Detect unlabeled break/continue that must be bound to the nearest enclosing
  -- loop label before lowering to Core gotos. Nested loops are handled in their
  -- own lowering branch and are intentionally not traversed here.
  | .BreakOrContinue none _ => true
  | .DeadEnd stm => hasUnlabeledLoopControl stm
  | .If _ b1 b2 =>
    hasUnlabeledLoopControl b1 || (b2.map hasUnlabeledLoopControl).getD false
  | .OpenInvariant stm => hasUnlabeledLoopControl stm
  | .ClosureInner body => hasUnlabeledLoopControl body
  | .AssertQuery _ body => hasUnlabeledLoopControl body
  | .Block stms => stms.any hasUnlabeledLoopControl
  | .Loop .. => false
  | .Reveal .. => false
  | _ => false

partial def bindUnlabeledLoopControlTo (loopLabel : String) : Stm → Stm
  -- Bind unlabeled break/continue to the nearest enclosing loop label.
  -- We intentionally do not recurse into nested loops: each nested loop binds
  -- its own unlabeled control-flow in its own lowering branch.
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

def mkQueryObligation (env : VarEnv) (label : String) (requires ensures : List Exp) :
    Except String (List Core.Statement) := do
  let reqs ← requires.mapM (expToCore env (some .Bool))
  let enss ← ensures.mapM (expToCore env (some .Bool))
  return [mkAssertStmt label (mkQueryObligationExpr reqs enss)]

mutual
  partial def stmToCore (env : VarEnv) (projLayouts : List ProjLayout)
      (mutArgMap : MutArgMap)
      (retVar? : Option (String × Typ)) :
    Stm → Except String (List Core.Statement)
  | .Call fn _typArgs args => do
    if isGhostPervasiveCallName fn then
      return []
    let argsFiltered := normalizeCallArgsForCallee env fn args
    let callee := CoreIdent.toPretty (identToCore fn)
    let lowered ← lowerMutCallArgs env projLayouts mutArgMap callee argsFiltered
    return lowered.pre ++ [mkCallStmt lowered.mutOuts callee lowered.argsCore] ++ lowered.post
  | .Assert exp
  | .AssertLean exp => do
    match exp with
    | .Unary (.HasType _) _ =>
      -- Verus emits HasType wrapper asserts for arithmetic checks in SST.
      -- We intentionally skip these here unless/until HasType semantics are
      -- modeled explicitly in Core.
      return []
    | _ =>
      let e ← expToCore env (some .Bool) exp
      return [mkAssertStmt "" e]
  | .AssertBitVector requires ensures =>
    -- Keep one VC for the bitvector query itself: requires ==> ensures.
    mkQueryObligation env "bitvector_query" requires ensures
  | .AssertQuery mode body =>
    match queryReqEnsFromBody body with
    | some (reqs, enss) =>
      mkQueryObligation env (assertQueryModeLabel mode) reqs enss
    | none =>
      -- Fallback for unexpected query-body shapes.
      stmToCore env projLayouts mutArgMap retVar? body
  | .AssertCompute exp => do
    let e ← expToCore env (some .Bool) exp
    return [mkAssertStmt "compute" e]
  | .Assume exp => do
    let e ← expToCore env (some .Bool) exp
    return [mkAssumeStmt "" e]
  | .Assign lhs lhsTy rhs lhsIsInit => do
    if shouldDropAssignAsForLoopScaffolding lhs then
      return []
    -- Locals are predeclared in procedure preludes; assignment sites always use `set`.
    let assignExprToLhs : CoreExpr → Except String (List Core.Statement) := fun (rhs' : CoreExpr) => do
      match lvalueVarName? lhs with
      | some lhsName =>
        return [mkSetStmt (varToCore lhsName) rhs']
      | none =>
        if lhsIsInit then
          throw s!"unsupported init assignment to projected l-value: {repr lhs}"
        let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
        return [mkSetStmt (varToCore rootName) updatedRoot]
    match rhs with
    | .Call fn _typArgs args => do
      let fnName := CallFun.name fn
      if isGhostPervasiveCallName fnName then
        return []
      let argsFiltered := normalizeCallArgsForCallee env fnName args
      let callee := CoreIdent.toPretty (identToCore fnName)
      if (lookupFnRetType env callee).isSome then
        -- Spec/prelude functions are expression-level in Core even when Verus
        -- serialized the source call in assignment position.
        let rhs' ← expToCore env (some lhsTy) rhs
        assignExprToLhs rhs'
      else
        if isIntoIterName fnName then
          match argsFiltered with
          | [arg] =>
            let rhs' ← expToCore env (some lhsTy) arg
            return (← assignExprToLhs rhs')
          | _ => pure ()
        if isIteratorNextName fnName && (optionTypAndElem? lhsTy).isNone then
          throw s!"iterator-next call has non-option lhs type: {repr lhsTy}"
        if isViewName fnName || isVecLenSpecName fnName || isVecLenExecName fnName
            || isVecIndexSpecName fnName || isVecIndexExecName fnName then
          let rhs' ← expToCore env (some lhsTy) rhs
          assignExprToLhs rhs'
        else
          let (destName, decl) ←
            match lvalueVarName? lhs with
            | some lhsName =>
              -- Locals are already predeclared; no init needed for direct l-values.
              pure (varToCore lhsName, [])
            | none =>
              -- Projected l-values need a temporary to receive the call result.
              let tmp := varToCore (projectedCallTmpName fnName lhs)
              let declTy := .forAll [] (monoTyOfTyp lhsTy)
              pure (tmp, [mkInitStmt tmp declTy declSentinel])
          let lowered ← lowerMutCallArgs env projLayouts mutArgMap callee argsFiltered
          let callStmt := mkCallStmt ([destName] ++ lowered.mutOuts) callee lowered.argsCore
          match lvalueVarName? lhs with
          | some _ =>
            return decl ++ lowered.pre ++ [callStmt] ++ lowered.post
          | none =>
            let rhsTmp := LExpr.fvar () destName (some (monoTyOfTyp lhsTy))
            let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhsTmp
            return decl ++ lowered.pre ++ [callStmt] ++ lowered.post ++
              [mkSetStmt (varToCore rootName) updatedRoot]
    | _ => do
      let rhs' ← expToCore env (some lhsTy) rhs
      assignExprToLhs rhs'
  | .DeadEnd stm =>
    stmToCore env projLayouts mutArgMap retVar? stm
  | .Return exp => do
    match exp, retVar? with
    | some e, some (retName, retTy) =>
      -- Unit-like returns (empty tuple/struct/enum) carry no payload.
      match e with
      | .EnumCtor _ "tuple%0" [] | .TupleCtor 0 [] | .StructCtor _ [] =>
        return [mkReturnStmt]
      | _ =>
        let rhs ← expToCore env (some retTy) e
        return [mkSetStmt (varToCore retName) rhs, mkReturnStmt]
    | _, _ => return [mkReturnStmt]
  | .BreakOrContinue label isBreak =>
    match label with
    | some l => return [mkExitToLabelStmt (sanitizeIdent l)]
    | none =>
      -- Unlabeled break/continue must be eliminated by structured loop
      -- reconstruction; emitting synthetic goto labels is not type-safe in Core.
      throw s!"unsupported unlabeled {(if isBreak then "break" else "continue")} after loop normalization"
  | .If cond b1 b2 => do
    let c ← expToCore env (some .Bool) cond
    let thenStms ← stmToCore env projLayouts mutArgMap retVar? b1
    let elseStms ← match b2 with
      | some s => stmToCore env projLayouts mutArgMap retVar? s
      | none => pure []
    return [mkIteStmt c thenStms elseStms]
  | .Loop _isForLoop label cond body invs decrease => do
    -- Verus emits SST guard shapes depending on `loop_isolation` (default is `true`):
    --   1) `loop_isolation(false)`: `cond = none`, guard appears in body prefix
    --      as `if (!guard) { break; }`.
    --   2) `loop_isolation(true)`: `cond = some (prefixStm, guardExpr)`, where
    --      `guardExpr` may reference temps defined in `prefixStm`.
    -- We support both by:
    --   - using `cond` directly when it is present, and
    --   - when `cond = none`, computing `guardFromBody?` via
    --     `extractLoopGuardFromBody` and using that in the `condExpr` branch below.
    let (guardFromBody?, body') :=
      match extractLoopGuardFromBody body with
      | some (g, b') => (some g, b')
      | none => (none, body)
    -- Keep emitted Core close to source: only synthesize a loop label when this
    -- loop actually contains unlabeled break/continue that need goto targets.
    let loopLabel? :=
      match label with
      | some l => some (sanitizeIdent l)
      | none =>
        let condNeeds := match cond with | some (s, _) => hasUnlabeledLoopControl s | none => false
        if condNeeds || hasUnlabeledLoopControl body' then
          some (implicitLoopLabel cond body)
        else
          none
    -- With `loop_isolation(true)`, `cond = some (prefixStm, guardExpr)`,
    -- where `guardExpr` may reference temps defined by `prefixStm`.
    -- We substitute those temp-prefix bindings into the guard expression so
    -- subsequent temp-inlining of `prefixStm` cannot leave a dangling temp var.
    let condTempSubsts : List (String × Exp) :=
      match cond with
      | some (Stm.Block stms, _) => (splitAssignPrefix stms).fst
      | some (s, _) =>
        match assignFromPrefix s with
        | some sub => [sub]
        | none => []
      | none => []
    let dropCondTempNames : List String :=
      match cond with
      | some (Stm.Block stms, _) => (splitDropCondTempPrefix stms).fst
      | some (s, _) =>
        match dropCondTempAssignFromPrefix s with
        | some n => [n]
        | none => []
      | none => []
    let condExpr ←
      match cond with
      | some (_, e) => expToCore env (some .Bool) (substExps condTempSubsts e)
      | none =>
        -- Fallback for `loop_isolation(false)`: when `cond = none`,
        -- use the guard recovered from the body prefix
        -- `[tmp-prefix]* ; if (!guard) { break; } ; ...`.
        match guardFromBody? with
        | some g => expToCore env (some .Bool) g
        | none => pure (LExpr.boolConst () true : CoreExpr)
    let condStmsRaw ← match cond with
      | some (s, _) =>
        let s' := match loopLabel? with | some l => bindUnlabeledLoopControlTo l s | none => s
        stmToCore env projLayouts mutArgMap retVar? s'
      | none => pure []
    -- Source-faithful cleanup: after substituting pure temp-prefix assignments
    -- into the loop guard, drop those synthetic temp statements from emitted Core.
    let condStms := dropTempPrefixCoreAssigns dropCondTempNames condStmsRaw
    -- Preserve loop invariants as exported by Verus SST.
    -- Do not drop/normalize for-loop ghost conjuncts here for faithful translation
    let invExprs ← loopInvariantToCore env invs
    -- Translate decreases clause to a Core loop measure (must type as `int`).
    -- Strata supports a single measure expression. When Verus supplies a
    -- multi-element decreases tuple we use the first element, as lexicographic
    -- ordering is not yet expressible in Core's single-measure slot.
    let measureExpr? ← match decrease with
      | [] => pure none
      | e :: _ => do
        -- Strata's loop measure slot is `int`-typed, so lower the selected
        -- Verus decreases expression with an explicit `int` expectation. When
        -- the expression still lowers through bitvector arithmetic (e.g.
        -- `usize` loop counters), cast the final result to `int`.
        let ce0 ← expToCore env (some .Int) e
        let ce := castExprToIntIfBitInfo (inferBitInfo env [] e) ce0
        pure (some ce)
    let bodyBound := match loopLabel? with | some l => bindUnlabeledLoopControlTo l body' | none => body'
    let bodyStms ← stmToCore env projLayouts mutArgMap retVar? bodyBound
    let loopStmt := mkLoop condExpr measureExpr? invExprs bodyStms
    let stmt := match loopLabel? with | some l => mkBlockStmt l [loopStmt] | none => loopStmt
    return condStms ++ [stmt]
  | .OpenInvariant stm =>
    stmToCore env projLayouts mutArgMap retVar? stm
  | .ClosureInner body =>
    stmToCore env projLayouts mutArgMap retVar? body
  | .Block stms =>
    stmListToCore env projLayouts mutArgMap retVar? stms
  | .Reveal .. =>
    -- All Reveal nodes should be rewritten by `expandReveals` before reaching
    -- `stmToCore`; otherwise drop it silently.
    return []

  partial def stmListToCore (env : VarEnv) (projLayouts : List ProjLayout)
      (mutArgMap : MutArgMap)
      (retVar? : Option (String × Typ)) :
    List Stm → Except String (List Core.Statement)
  | stms =>
    -- Normalize singleton wrapper blocks first so sequence-sensitive patterns
    -- (e.g. query-scaffolding assume stripping) can match reliably.
    let normalized := (flattenSeqBlocks (inlineTemps stms)).map stripSingletonBlocks
    stmListToCoreAux env projLayouts mutArgMap retVar? normalized

  partial def stmListToCoreAux (env : VarEnv) (projLayouts : List ProjLayout)
      (mutArgMap : MutArgMap)
      (retVar? : Option (String × Typ)) :
    List Stm → Except String (List Core.Statement)
  | (.BreakOrContinue none true) :: (.Assume (.Const (.Bool false))) :: rest => do
    -- Verus often lowers `break` in dead-end branches as `break; assume false;`.
    -- Keep only `assume false` to avoid introducing unresolved break labels.
    let s2 ← stmListToCoreAux env projLayouts mutArgMap retVar? rest
    return [mkAssumeStmt "" (LExpr.boolConst () false)] ++ s2
  | a :: (.Assume e) :: next :: rest =>
    -- Keep source-facing assert shape: drop SST echo assumptions `assert E; assume E`.
    if isAssertAssumeEcho a e then
      stmListToCoreAux env projLayouts mutArgMap retVar? (a :: next :: rest)
    -- Synthetic query prefix shape: `assert true; assume E; <query>`.
    -- Drop the no-op `assert true` together with the scaffolding assume.
    else if isTrivialTrueAssert a && isQueryScaffoldingAssume e next then
      stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
    else do
      let s1 ← stmToCore env projLayouts mutArgMap retVar? a
      let s2 ← stmListToCoreAux env projLayouts mutArgMap retVar? ((.Assume e) :: next :: rest)
      return s1 ++ s2
  | (.Assume e) :: next :: rest =>
    -- Drop only query-internal `assume ensure` scaffolding inserted by Verus
    -- for `assert ... by (...)` lowering. Keep all other assumes.
    if isQueryScaffoldingAssume e next then
      stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
    else do
      let s1 ← stmToCore env projLayouts mutArgMap retVar? (.Assume e)
      let s2 ← stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
      return s1 ++ s2
  | a :: next :: rest =>
    -- Keep source-facing assert shape in 2-statement tails too.
    match next with
    | .Assume e =>
      if isAssertAssumeEcho a e then
        stmListToCoreAux env projLayouts mutArgMap retVar? (a :: rest)
      else do
        let s1 ← stmToCore env projLayouts mutArgMap retVar? a
        let s2 ← stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
        return s1 ++ s2
    | _ =>
      -- Verus query lowering can emit a synthetic `assert true` right before the
      -- actual query statement. Drop only this query-adjacent no-op assert.
      if isTrivialTrueAssert a && isQueryStmt next then
        stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
      else do
        let s1 ← stmToCore env projLayouts mutArgMap retVar? a
        let s2 ← stmListToCoreAux env projLayouts mutArgMap retVar? (next :: rest)
        return s1 ++ s2
  | [stm] =>
    stmToCore env projLayouts mutArgMap retVar? stm
  | [] => return []
end

def dedupLocals (locals : List (String × Typ)) : List (String × Typ) :=
  locals.foldl (init := []) (fun acc (n, t) =>
    if acc.any (fun (n', _) => n' == n) then acc else acc ++ [(n, t)])

-- `Iterator::next` lowering introduces internal temporaries for start/end snapshots.
-- Predeclare them so assignment statements can emit plain `set` commands.
private def rangeIterTempLocalsFromAssign (lhsTy : Typ) (rhs : Exp) : List (String × Typ) :=
  match rhs with
  | .Call fn _ args =>
    let fn := CallFun.name fn
    if isIteratorNextName fn then
      match optionTypAndElem? lhsTy, args with
      | some (_, idxTy), [iterArg] =>
        match vecVarFromExp iterArg with
        | some iterVar => [(s!"{iterVar}_next_start", idxTy), (s!"{iterVar}_next_end", idxTy)]
        | none => []
      | _, _ => []
    else
      []
  | _ => []

partial def collectSetVars : Stm → List (String × Typ)
  -- Track non-init assignments. This is used to predeclare synthetic
  -- variables that are emitted as plain lhs names.
  | .Assign lhs lhsTy rhs lhsIsInit =>
    let base :=
      if lhsIsInit then
        []
      else
        match lvalueVarName? lhs with
        | some name => [(name, lhsTy)]
        | none => []
    base ++ rangeIterTempLocalsFromAssign lhsTy rhs
  | .AssertQuery _ body => collectSetVars body
  | .DeadEnd stm => collectSetVars stm
  | .If _cond b1 b2 =>
    collectSetVars b1 ++ (b2.map collectSetVars).getD []
  | .Loop _isForLoop _label cond body _invs _decrease =>
    let condVars := match cond with
      | some (s, _) => collectSetVars s
      | none => []
    condVars ++ collectSetVars body
  | .OpenInvariant stm => collectSetVars stm
  | .ClosureInner body => collectSetVars body
  | .Block stms => stms.flatMap collectSetVars
  | _ => []

/-! ## Declaration Translation -/

def signatureOf (decls : List (String × Typ)) :
    @Lambda.LMonoTySignature Visibility :=
  decls.map (fun (n, t) => (varToCore n, monoTyOfTyp t))

def signatureOfVec (decls : List (String × Typ)) :
    @Lambda.LMonoTySignature Visibility :=
  signatureOf (expandVecDecls decls)

partial def typTypeVars : Typ → List String
  | .TypParam n => [sanitizeIdent n]
  | .Tuple t1 t2 => (typTypeVars t1 ++ typTypeVars t2).eraseDups
  | .Array t => typTypeVars t
  | .SpecFn ps ret => ((ps.flatMap typTypeVars) ++ typTypeVars ret).eraseDups
  | .Decorated _ t => typTypeVars t
  | .Struct _ ps => (ps.flatMap typTypeVars).eraseDups
  | .Enum _ ps => (ps.flatMap typTypeVars).eraseDups
  | _ => []

def typeArgsFromTyps (tys : List Typ) : List String :=
  (tys.flatMap typTypeVars).eraseDups

def typeArgsFromDecls (decls : List (String × Typ)) : List String :=
  typeArgsFromTyps (decls.map Prod.snd)

partial def collectMutArgMapFromDecls (decls : List Decl) : MutArgMap :=
  let rec go (acc : MutArgMap) : List Decl → MutArgMap
    | [] => acc
    | d :: rest =>
      let acc' :=
        match d with
        | .execFn f =>
          let infos := mutArgInfos f.inputs
          if infos.isEmpty then acc else acc.insert (CoreIdent.toPretty (identToCore f.name)) infos
        | .mutualBlock ds => go acc ds
        | _ => acc
      go acc' rest
  go (∅ : MutArgMap) decls

private partial def collectNoParamFnNamesFromDecls : List Decl → List String
  | [] => []
  | d :: rest =>
    let here :=
      match d with
      | .specFn f | .proofFn f | .execFn f =>
        if f.inputs.isEmpty then [CoreIdent.toPretty (identToCore f.name)] else []
      | .func f =>
        if f.decls.isEmpty then [CoreIdent.toPretty (identToCore f.name)] else []
      | .mutualBlock ds => collectNoParamFnNamesFromDecls ds
      | _ => []
    (here ++ collectNoParamFnNamesFromDecls rest).eraseDups

/-! ### Opaque/Reveal: SpecFn lookup table

`reveal(f)` in Verus is lowered to `Fuel(f, 1)` in the SST JSON.  We parse
it as `Stm.Reveal fn fuel`.  To translate it to Strata Core we need the
defining equation of `f` — i.e. its parameter list and body — so we build a
lookup table from the declaration list before translating procedure bodies.
-/

/-- Map from spec-function identifiers to their VLIR definitions. -/
abbrev SpecFnMap := Std.HashMap Ident SpecFn

/-- Add spec-function return and parameter types to a `VarEnv` so that
    `inferBitInfo` can determine bitvector widths and `expToCoreWithBound`
    can insert coercions at call sites. -/
private def addFnRetTypes (env : VarEnv) (sfMap : SpecFnMap) : VarEnv :=
  sfMap.fold (init := env) (fun acc name sf =>
    let fnStr := CoreIdent.toPretty (identToCore name)
    let acc := acc.insert (fnRetKey fnStr) sf.returnType
    -- Store each parameter type for call-site coercion insertion.
    sf.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
      acc.insert (fnParamKey fnStr idx) ty))

/-- Add parameter types from all declarations (proof fns, exec fns) so that
    procedure call sites can also get coercion insertion. -/
private partial def addAllFnParamTypes (env : VarEnv) (decls : List Decl) : VarEnv :=
  decls.foldl (init := env) (fun acc d =>
    match d with
    | .proofFn f =>
      let fnStr := CoreIdent.toPretty (identToCore f.name)
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .execFn f =>
      let fnStr := CoreIdent.toPretty (identToCore f.name)
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .mutualBlock ds => addAllFnParamTypes acc ds
    | _ => acc)

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

/-- True when the spec function has type-parameter variables in its signature. -/
private def specFnIsGeneric (f : SpecFn) : Bool :=
  !(typeArgsFromDecls f.inputs ++ typeArgsFromTyps [f.returnType]).isEmpty

/-- Build the defining-equation assumption for `reveal(f)`.

For a spec function `f(x₁: T₁, …, xₙ: Tₙ): R { body }`:
- 0 params → `assume [reveal_f]: f() == body;`
- n params → `assume [reveal_f]: (forall x₁: T₁, …, xₙ: Tₙ :: f(x₁, …, xₙ) == body);`

Returns `none` for generic spec fns because the Fuel JSON does not carry the
type-argument instantiation (e.g. `reveal(g::<u8>)` loses the `<u8>` part).
-/
private def mkRevealAssume (f : SpecFn) : Option Stm :=
  if specFnIsGeneric f then none
  else match f.body with
  | none => none  -- uninterpreted function; nothing to reveal
  | some body =>
    let callArgs := f.inputs.map (fun (x, _) => Exp.Var x)
    let call := Exp.Call (.Fun f.name) [] callArgs
    let eq := Exp.Binary (.Eq .Spec) call body
    let equation :=
      if f.inputs.isEmpty then eq
      else Exp.Bind (.Quant .Forall f.inputs []) eq
    some (.Assume equation)

/-- Recursively rewrite `Stm.Reveal fn fuel` into `Stm.Assume` using the
spec-fn lookup table.  Unknown or generic functions are silently dropped
(generic reveals need type-argument instantiation we don't yet have). -/
partial def expandReveals (sfMap : SpecFnMap) : Stm → Stm
  | .Reveal fn _fuel =>
    match sfMap.get? fn with
    | some f => (mkRevealAssume f).getD (.Block [])
    | none => .Block []  -- unknown function; drop silently
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

def mkChecks (env : VarEnv) (checkPrefix : String) (exps : List Exp) :
    Except String (ListMap CoreLabel Procedure.Check) := do
  let exprs ← exps.mapM (expToCore env (some .Bool))
  return exprs.zipIdx.map (fun (e, i) => (s!"{checkPrefix}{i}", { expr := e, attr := .Default }))

private def concatRefLists {α : Type} (xss : List (List α)) : List α :=
  xss.foldr (· ++ ·) []

private partial def stmtModifiedVars : Core.Statement → List CoreIdent
  | .cmd (.cmd (.init name _ e _)) =>
    match e with
    | some rhs => if isDeclSentinel rhs then [] else [name]
    | none => []
  | .cmd (.cmd (.set name _ _)) => [name]
  | .cmd (.cmd (.havoc name _)) => [name]
  | .cmd (.cmd (.assert _ _ _)) => []
  | .cmd (.cmd (.assume _ _ _)) => []
  | .cmd (.cmd (.cover _ _ _)) => []
  | .cmd (.call lhs _ _ _) => lhs
  | .block _ ss _ => (ss.flatMap stmtModifiedVars).eraseDups
  | .ite _ t e _ => (t.flatMap stmtModifiedVars ++ e.flatMap stmtModifiedVars).eraseDups
  | .loop _ _ _ body _ => (body.flatMap stmtModifiedVars).eraseDups
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

private def stmtsModifiedVars (ss : List Core.Statement) : List CoreIdent :=
  (ss.flatMap stmtModifiedVars).eraseDups

private partial def stmtDeclOnlyLocals : Core.Statement → List CoreIdent
  | .cmd (.cmd (.init name _ e _)) =>
    match e with
    | some rhs => if isDeclSentinel rhs then [name] else []
    | none => [name]
  | .cmd _ => []
  | .block _ ss _ => (ss.flatMap stmtDeclOnlyLocals).eraseDups
  | .ite _ t e _ => (t.flatMap stmtDeclOnlyLocals ++ e.flatMap stmtDeclOnlyLocals).eraseDups
  | .loop _ _ _ body _ => (body.flatMap stmtDeclOnlyLocals).eraseDups
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

private def stmtsDeclOnlyLocals (ss : List Core.Statement) : List CoreIdent :=
  (ss.flatMap stmtDeclOnlyLocals).eraseDups

-- Infer `modifies` from actual write-sites in the translated body.
-- We exclude inputs/outputs and declaration-only locals, leaving potential globals.
private def inferProcModifies (p : Core.Procedure) : List CoreIdent :=
  let written := stmtsModifiedVars p.body
  let locals := stmtsDeclOnlyLocals p.body
  let disallowed := (ListMap.keys p.header.inputs ++ ListMap.keys p.header.outputs ++ locals).eraseDups
  written.filter (fun v => !disallowed.contains v) |>.eraseDups

/-- Extract the decreases measure expression(s) from a function/procedure body.
    Verus encodes `decreases n` as an `Assign` statement
    `decrease%init0 := n` at the start of the body `Block`.
    We collect the RHS of every such assignment. -/
private def collectDecreasesExps : Stm → List Exp
  | .Assign (.Var name) _ rhs _ =>
    if name.startsWith "decrease" then [rhs] else []
  | .Block stms => stms.flatMap collectDecreasesExps
  | _ => []

/-- True when a statement is a decrease-related artifact that should be stripped
    from the translated output for faithful source-level representation.
    Matches: `decrease%init*` assignments and `CheckDecreaseInt` assertions. -/
private def isDecreaseArtifact : Stm → Bool
  | .Assign (.Var name) _ _ _ => name.startsWith "decrease"
  | .Call fn _ _ => toString fn |>.startsWith "CheckDecrease"
  | .Assert (.Call fn _ _) => -- assert CheckDecreaseInt(...)
    toString (CallFun.name fn) |>.startsWith "CheckDecrease"
  | .Assert (.Var name) => name.startsWith "CheckDecrease"
  | _ => false

/-- True when a VLIR statement tree contains a `Return` node. -/
private partial def hasReturnStm : Stm → Bool
  | .Return _ => true
  | .Block stms => stms.any hasReturnStm
  | .If _ b1 b2 => hasReturnStm b1 || (b2.map hasReturnStm |>.getD false)
  | .DeadEnd stm => hasReturnStm stm
  | _ => false

/-- True when a statement is `Assume(false)` — used to strip dead-code
    markers that Verus inserts after `Return`. -/
private def isAssumeFalse : Stm → Bool
  | .Assume (.Const (.Bool false)) => true
  | _ => false

/-- Strip `Assume(false)` statements that follow `Return` in a block.
    Verus SST inserts these to mark unreachable code after early returns.
    Since we emit a return sentinel, these are no longer needed. -/
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
    -- Drop all trailing Assume(false) after a Return.
    .Return e :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
  | (.Block stms) :: rest =>
    let stripped := .Block (stripReturnAssumeFalse stms)
    -- If the block contained a Return, also strip trailing Assume(false).
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

/-- Strip decrease-related artifacts from a statement tree.
    Removes `decrease%init*` assigns and `CheckDecreaseInt` assertions
    while preserving the rest of the body structure. -/
private partial def stripDecreaseArtifacts : Stm → Stm
  | .Block stms =>
    .Block (stms.filter (!isDecreaseArtifact ·) |>.map stripDecreaseArtifacts)
  | .If cond b1 b2 =>
    .If cond (stripDecreaseArtifacts b1) (b2.map stripDecreaseArtifacts)
  | .DeadEnd stm => .DeadEnd (stripDecreaseArtifacts stm)
  | .Loop isFor label cond body invs dec =>
    .Loop isFor label cond (stripDecreaseArtifacts body) invs dec
  | stm => stm

def specFnToCore (noParamFns : List String)
    (emitBody : Bool) (f : SpecFn) (sfMap : SpecFnMap := (∅ : SpecFnMap)) : Except String Core.Function := do
  let env := addFnRetTypes (addNoParamFnMarkers (envFromDecls f.inputs) noParamFns) sfMap
  let typeArgs := (typeArgsFromDecls f.inputs ++ typeArgsFromTyps [f.returnType]).eraseDups
  -- Recursion metadata comes directly from Verus JSON (`has.is_recursive`) and
  -- parsed termination-check hints (`recursiveCasesIdxHint`).
  let recCasesIdx? := f.recursiveCasesIdxHint
  let isRecursive := f.isRecursive
  let attrs : Array Strata.DL.Util.FuncAttr :=
    match recCasesIdx? with
    | some idx => #[.inlineIfConstr idx]
    | none => #[]
  -- `SpecFn.decreases` is preserved in VLIR but not stored in the Core `Func`
  -- AST (which has no function-level decreases slot).  The decreases comment
  -- is built in `declsToProgram` from a side map and injected by the
  -- pretty-printer, avoiding misuse of the semantic `axioms` field.
  let body? ←
    match f.body with
    | none => pure none  -- uninterpreted: always declaration-only
    | some bodyExp =>
      if emitBody then
        some <$> expToCore env (some f.returnType) bodyExp
      else
        pure none
  return {
    name := identToCore f.name
    typeArgs := typeArgs
    isRecursive := isRecursive
    inputs := signatureOf f.inputs
    output := monoTyOfTyp f.returnType
    body := body?
    attr := attrs
  }

def proofFnToCore (noParamFns : List String) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ProofFn) (allDecls : List Decl := []) : Except String Core.Procedure := do
  let inputNames := f.inputs.map Prod.fst
  let hasRet :=
    match f.returnType with
    | .Unit | .Empty => false
    | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let retNames := if hasRet then [f.retName] else []
  -- Extract decreases expressions before stripping artifacts.
  let decreasesExps : List Exp := match f.body with
    | some body => collectDecreasesExps body
    | none => []
  let bodyStm? := f.body.map (fun b =>
    let b := expandReveals sfMap b
    let b := stripDecreaseArtifacts b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s)
  let setVars :=
    match bodyStm? with
    | some body => collectSetVars body
    | none => []
  let declaredInInputsRetOrLocals := fun (n : String) =>
    inputNames.any (fun x => x == n) ||
    retNames.any (fun x => x == n) ||
    f.locals.any (fun (ln, _) => ln == n)
  let implicitSetLocals := dedupLocals <| setVars.filter (fun (n, _) => !declaredInInputsRetOrLocals n)
  let localsAll := dedupLocals <| (f.locals.filter (fun (n, _) =>
    !(inputNames.any (fun x => x == n) || retNames.any (fun x => x == n))) ++ implicitSetLocals)
  let localsAll := localsAll.filter (fun (n, t) =>
    !shouldDropForLoopScaffoldingLocal n && !isUnitLikeTyp t)
  let localsDecls := localsAll
  let outputs := retDecls
  let env := addAllFnParamTypes (addFnRetTypes (addNoParamFnMarkers (envFromDecls (expandVecDecls (f.inputs ++ outputs ++ localsAll))) noParamFns) sfMap) allDecls
  let typeArgs := typeArgsFromDecls (f.inputs ++ outputs ++ localsAll)
  let pre ← mkChecks env "requires_" f.requires
  let post ← mkChecks env "ensures_" f.ensures
  let retVar? := if hasRet then some (f.retName, f.returnType) else none
  -- Translate decreases expressions for the comment.
  let decreasesCoreExprs ← decreasesExps.mapM (expToCore env none)
  let body ←
    match bodyStm? with
    | some stm => stmToCore env projLayouts mutArgMap retVar? stm
    | none => pure []
  -- Filter out `decrease%init*` local declarations.
  let localDecls :=
    localsDecls.filter (fun (n, _) => !n.startsWith "decrease") |>.map (fun (n, t) =>
      mkInitStmt (varToCore n) (.forAll [] (monoTyOfTyp t)) declSentinel)
  -- Build a `// decreases (expr)` comment statement.  We encode this as an
  -- `assume __decreases_comment__(e₁, …)` sentinel that the pretty-printer
  -- recognises and renders as a comment.
  let decreasesStmts := if decreasesCoreExprs.isEmpty then [] else
    let marker := LExpr.op () (CoreIdent.unres "__decreases_comment__") none
    let e := LExpr.mkApp () marker decreasesCoreExprs
    [mkAssumeStmt "__decreases__" e]
  let proc : Core.Procedure := {
    header := {
      name := identToCore f.name
      typeArgs := typeArgs
      inputs := signatureOfVec f.inputs
      outputs := signatureOfVec outputs
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body :=
      let inner := localDecls ++ body
      -- If the body contains early returns (exit __return__), wrap in a
      let hasReturn := f.body.map (fun b => hasReturnStm b) |>.getD false
      let inner := if hasReturn then stripCoreAssumeFalse inner else inner
      -- Return is encoded as `assert [__return__]: true`, rendered as `// return;`.
      decreasesStmts ++ inner
  }
  let modifies := inferProcModifies proc
  return { proc with spec := { proc.spec with modifies := modifies } }

def execFnToCore (noParamFns : List String) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ExecFn) (allDecls : List Decl := []) : Except String Core.Procedure := do
  let mutOutDecls :=
    f.inputs.filterMap (fun (n, t) =>
      (mutRefPayload? t).map (fun payloadTy => (n, s!"{n}_out", payloadTy)))
  let mutRenames := mutOutDecls.map (fun (n, outName, _) => (n, outName))
  -- Extract decreases expressions before stripping artifacts.
  let decreasesExps : List Exp := collectDecreasesExps f.body
  let rewrittenBody :=
    let b := stripDecreaseArtifacts (expandReveals sfMap (applyNameSubstsStm mutRenames f.body))
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s
  let rewrittenEnsures := f.ensures.map (applyNameSubstsExp mutRenames)
  let hasRet :=
    match f.returnType with
    | .Unit | .Empty => false
    | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let mutOutputDecls := mutOutDecls.map (fun (_, outName, payloadTy) => (outName, payloadTy))
  let inputNames := f.inputs.map Prod.fst
  let retNames := (if hasRet then [f.retName] else []) ++ mutOutputDecls.map Prod.fst
  let setVars := collectSetVars rewrittenBody
  let declaredInInputsRetOrLocals := fun (n : String) =>
    inputNames.any (fun x => x == n) ||
    retNames.any (fun x => x == n) ||
    f.locals.any (fun (ln, _) => ln == n)
  let implicitSetLocals := dedupLocals <| setVars.filter (fun (n, _) => !declaredInInputsRetOrLocals n)
  let localsAll := dedupLocals <| (f.locals.filter (fun (n, _) =>
    !(inputNames.any (fun x => x == n) || retNames.any (fun x => x == n))) ++ implicitSetLocals)
  let localsAll := localsAll.filter (fun (n, t) =>
    !shouldDropForLoopScaffoldingLocal n && !isUnitLikeTyp t)
  let localsDecls := localsAll
  let outputs := retDecls ++ mutOutputDecls
  let env := addAllFnParamTypes (addFnRetTypes (addNoParamFnMarkers
    (envFromDecls (expandVecDecls (f.inputs ++ outputs ++ localsAll))) noParamFns) sfMap) allDecls
  let typeArgs := typeArgsFromDecls (f.inputs ++ outputs ++ localsAll)
  let pre ← mkChecks env "requires_" f.requires
  let post ← mkChecks env "ensures_" rewrittenEnsures
  let retVar? := if hasRet then some (f.retName, f.returnType) else none
  -- Translate decreases expressions for the comment.
  let decreasesCoreExprs ← decreasesExps.mapM (expToCore env none)
  let body ← stmToCore env projLayouts mutArgMap retVar? rewrittenBody
  let mutOutInits :=
    mutOutDecls.map (fun (inName, outName, payloadTy) =>
      let rhs := LExpr.fvar () (varToCore inName) (some (monoTyOfTyp payloadTy))
      mkSetStmt (varToCore outName) rhs)
  -- Declaration-only locals are represented with a sentinel RHS and rendered
  -- by the pretty-printer as `var x : T;`
  let localDecls :=
    localsDecls.filter (fun (n, _) => !n.startsWith "decrease") |>.map (fun (n, t) =>
      mkInitStmt (varToCore n) (.forAll [] (monoTyOfTyp t)) declSentinel)
  let decreasesStmts := if decreasesCoreExprs.isEmpty then [] else
    let marker := LExpr.op () (CoreIdent.unres "__decreases_comment__") none
    let e := LExpr.mkApp () marker decreasesCoreExprs
    [mkAssumeStmt "__decreases__" e]
  let proc : Core.Procedure := {
    header := {
      name := identToCore f.name
      typeArgs := typeArgs
      inputs := signatureOfVec f.inputs
      outputs := signatureOfVec outputs
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body :=
      let inner := localDecls ++ mutOutInits ++ body
      let hasReturn := hasReturnStm f.body
      let inner := if hasReturn then stripCoreAssumeFalse inner else inner
      decreasesStmts ++ inner
  }
  let modifies := inferProcModifies proc
  return { proc with spec := { proc.spec with modifies := modifies } }

-- TODO
def funcCheckSstToCore (noParamFns : List String) (f : FuncCheckSst) : Except String Core.Procedure := do
  let env := addNoParamFnMarkers (envFromDecls f.decls) noParamFns
  let pre ← mkChecks env "requires_" f.reqs
  let post ← mkChecks env "ensures_" f.postCondition
  let proc : Core.Procedure := {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf f.decls
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body := []
  }
  let modifies := inferProcModifies proc
  return { proc with spec := { proc.spec with modifies := modifies } }

partial def monoTyTypeVars : LMonoTy → List String
  | .ftvar n => [sanitizeIdent n]
  | .tcons _ args => (args.flatMap monoTyTypeVars).eraseDups
  | _ => []

def normalizeTypeParams (params : List String) : List String :=
  let ps := (params.map sanitizeIdent).filter (fun p => !p.isEmpty && p != "implementMePlease")
  ps.eraseDups

def chooseTypeArgs (declParams fromFields : List String) : List String :=
  let ps := normalizeTypeParams declParams
  let fs := (fromFields.map sanitizeIdent).filter (fun p => !p.isEmpty) |>.eraseDups
  if ps.isEmpty then fs else ps

def structToCoreTypeDecl (s : Struct) : Core.TypeDecl :=
  let dtName := datatypeNameOf s.name
  let ctorId := structCtorIdentOf s.name
  let ctorFields : List (CoreIdent × LMonoTy) :=
    s.fields.map (fun (field, ty) =>
      (fieldAccessorIdentOf field, monoTyOfTyp ty))
  let inferredTypeArgs := (ctorFields.map Prod.snd).flatMap monoTyTypeVars |>.eraseDups
  let constr : LConstr Visibility :=
    { name := ctorId
      args := ctorFields
      testerName := s!"{dtName}..is{CoreIdent.toPretty ctorId}" }
  let d : LDatatype Visibility :=
    { name := dtName
      typeArgs := chooseTypeArgs s.typeParams inferredTypeArgs
      constrs := [constr]
      constrs_ne := by simp }
  .data [d]

def enumToCoreTypeDecl (e : Enum) : Except String Core.TypeDecl := do
  let dtName := datatypeNameOf e.name
  let constrs : List (LConstr Visibility) :=
    e.fields.map (fun field =>
      match field with
      | .labeled variant data =>
        let ctorId := enumCtorIdentOf e.name variant
        let args := data.map (fun (fname, ty) =>
          (fieldAccessorIdentOf (projFieldNameOf e.name variant fname), monoTyOfTyp ty))
        { name := ctorId
          args := args
          testerName := enumTesterNameOf e.name variant }
      | .tuple variant ts =>
        let ctorId := enumCtorIdentOf e.name variant
        let args := ts.zipIdx.map (fun (ty, i) =>
          let field := s!"{dtName}_{sanitizeIdent variant}_{i}"
          (CoreIdent.unres field, monoTyOfTyp ty))
        { name := ctorId
          args := args
          testerName := enumTesterNameOf e.name variant })
  let inferredTypeArgs := (constrs.flatMap (fun c => c.args.map Prod.snd)).flatMap monoTyTypeVars |>.eraseDups
  let typeArgs := chooseTypeArgs e.typeParams inferredTypeArgs
  match constrs with
  | [] =>
    -- Opaque/imported enum shards can serialize with zero variants.
    -- Lower these to an abstract type constructor so references remain well-formed.
    return .con { name := dtName, params := typeArgs }
  | c :: cs =>
    let d : LDatatype Visibility :=
      { name := dtName
        typeArgs := typeArgs
        constrs := c :: cs
        constrs_ne := by simp }
    return .data [d]

partial def declToCore (noParamFns : List String)
    (projLayouts : List ProjLayout) (mutArgMap : MutArgMap) (sfMap : SpecFnMap)
    (allDecls : List Decl := []) :
    Decl → Except String (List Core.Decl)
  | .assertion _ =>
    -- Drop top-level `DeclType: Assert` wrappers for Core emission.
    -- Their obligations already appear in enclosing function/procedure bodies.
    -- (These declarations remain useful in the Verus->Lean pipeline.)
    return []
  | .specFn f => do
    let fn ← specFnToCore noParamFns (!f.isOpaque) f sfMap
    return [Core.Decl.func fn]
  | .proofFn f => do
    let p ← proofFnToCore noParamFns projLayouts mutArgMap sfMap f allDecls
    return [Core.Decl.proc p]
  | .execFn f => do
    let isDeclOnly := match f.body with | .Block [] => true | _ => false
    -- `Iterator::next` in exported decls is often trait-generic over
    -- associated type `Item`, which Strata currently cannot typecheck.
    -- Emit a concrete range/usize stub for current for-loop lowering targets.
    if isDeclOnly && isIteratorNextName f.name then
      return [Core.Decl.proc {
        header := {
          name := identToCore f.name
          typeArgs := []
          inputs := [(CoreIdent.unres "self", .tcons "Ops_Range_range" [.bitvec usizeBitWidth])]
          outputs := [(CoreIdent.unres "_pct_return", .tcons "Option_option" [.bitvec usizeBitWidth])]
        }
        spec := { modifies := [], preconditions := [], postconditions := [] }
        body := []
      }]
    let p ← execFnToCore noParamFns projLayouts mutArgMap sfMap f allDecls
    return [Core.Decl.proc p]
  | .func f => do
    let p ← funcCheckSstToCore noParamFns f
    return [Core.Decl.proc p]
  | .struct s =>
    return [Core.Decl.type (structToCoreTypeDecl s)]
  | .enum e => do
    let dt ← enumToCoreTypeDecl e
    return [Core.Decl.type dt]
  | .mutualBlock ds => do
    -- Translate all declarations in the mutual block.
    let mutualParts ← ds.mapM (fun d =>
      match d with
      | .specFn f => do
        let fn ← specFnToCore noParamFns (!f.isOpaque) f sfMap
        return (.inl fn : Sum Core.Function (List Core.Decl))
      | _ => do
        let newDecls ← declToCore noParamFns projLayouts mutArgMap sfMap allDecls d
        return (.inr newDecls))
    -- Partition into spec functions (left) and other declarations (right).
    let specFns := mutualParts.filterMap (fun s => match s with
      | .inl f => some f | _ => none)
    let otherDecls := mutualParts.flatMap (fun s => match s with
      | .inr ds => ds | _ => [])
    -- Group spec functions into a recFuncBlock for mutual recursion.
    let groupedDecls :=
      if specFns.isEmpty then []
      else [Core.Decl.recFuncBlock specFns .empty]
    return groupedDecls ++ otherDecls

/-! ## Synthetic Helper Pruning

With `--export-lean-all`, Verus may serialize many synthesized helper
declarations (e.g. `impl&%N::arrow_*`, `alloc::vec::impl&%1::len`) even when
they are not reachable from translated bodies/specs. After sanitization, these
commonly contain an `Impl__` segment.

To reduce emitted Core noise, we keep only synthetic helper declarations that
are reachable (transitively) from non-helper declarations.

TODO: if/when Verus export becomes reachability-minimized for
`--export-lean-all`, this pass can be reduced or removed.
-/

-- Name-level predicate for synthesized helper declarations after
-- sanitization/projection (e.g. `impl__N_arrow_*`, `Vec_Impl__1_len`).
def isSyntheticHelperName (s : String) : Bool :=
  s.startsWith "impl__" || s.startsWith "Impl__" || (s.find? "_Impl__").isSome

private def joinRefs (xss : List (List String)) : List String :=
  (xss.foldr (· ++ ·) []).eraseDups

private def exprVarNames (e : CoreExpr) : List String :=
  ((Lambda.LExpr.LExpr.getVars e).map CoreIdent.toPretty).eraseDups

private def collectVarNamesFromChecks (checks : ListMap CoreLabel Core.Procedure.Check) : List String :=
  joinRefs <| checks.values.map (fun c => exprVarNames c.expr)

-- Collect variable touches while ignoring declaration-only locals
-- (`var x : T;` represented as `init x T __verus_decl__`).
private partial def stmtTouchedVarsExcludingDeclOnly : Core.Statement → List String
  | .cmd (.cmd (.init name _ e _)) =>
    match e with
    | some rhs =>
      if isDeclSentinel rhs then
        []
      else
        (CoreIdent.toPretty name :: exprVarNames rhs).eraseDups
    | none =>
      [CoreIdent.toPretty name]
  | .cmd (.cmd (.set name e _)) =>
    (CoreIdent.toPretty name :: exprVarNames e).eraseDups
  | .cmd (.cmd (.havoc name _)) =>
    [CoreIdent.toPretty name]
  | .cmd (.cmd (.assert _ e _)) => exprVarNames e
  | .cmd (.cmd (.assume _ e _)) => exprVarNames e
  | .cmd (.cmd (.cover _ e _)) => exprVarNames e
  | .cmd (.call lhs _ args _) =>
    joinRefs [(lhs.map CoreIdent.toPretty), joinRefs <| args.map exprVarNames]
  | .block _ ss _ => joinRefs <| ss.map stmtTouchedVarsExcludingDeclOnly
  | .ite cond t e _ =>
    joinRefs [exprVarNames cond, joinRefs (t.map stmtTouchedVarsExcludingDeclOnly), joinRefs (e.map stmtTouchedVarsExcludingDeclOnly)]
  | .loop guard measure invariant body _ =>
    let measureRefs := match measure with | some m => exprVarNames m | none => []
    let invariantRefs := joinRefs <| invariant.map exprVarNames
    joinRefs [exprVarNames guard, measureRefs, invariantRefs, joinRefs (body.map stmtTouchedVarsExcludingDeclOnly)]
  | .exit _ _ => []
  | .funcDecl decl _ =>
    let bodyRefs := (decl.body.map exprVarNames).getD []
    let axiomRefs := joinRefs <| decl.axioms.map exprVarNames
    let preRefs := joinRefs <| decl.preconditions.map (fun p => exprVarNames p.expr)
    joinRefs [bodyRefs, axiomRefs, preRefs]
  | .typeDecl _ _ => []

private def stmtsTouchedVarsExcludingDeclOnly (ss : List Core.Statement) : List String :=
  joinRefs <| ss.map stmtTouchedVarsExcludingDeclOnly

private partial def pruneUnusedDeclOnlyStmt
    (usedVars : List String) : Core.Statement → Option Core.Statement
  | .cmd (.cmd (.init name ty e md)) =>
    match e with
    | some rhs =>
      if isDeclSentinel rhs && !usedVars.contains (CoreIdent.toPretty name) then
        none
      else
        some (.cmd (.cmd (.init name ty e md)))
    | none =>
      some (.cmd (.cmd (.init name ty e md)))
  | .cmd c => some (.cmd c)
  | .block label ss md =>
    some (.block label (ss.filterMap (pruneUnusedDeclOnlyStmt usedVars)) md)
  | .ite cond t e md =>
    some (.ite cond (t.filterMap (pruneUnusedDeclOnlyStmt usedVars)) (e.filterMap (pruneUnusedDeclOnlyStmt usedVars)) md)
  | .loop guard measure invariant body md =>
    some (.loop guard measure invariant (body.filterMap (pruneUnusedDeclOnlyStmt usedVars)) md)
  | .exit l md => some (.exit l md)
  | .funcDecl decl md => some (.funcDecl decl md)
  | .typeDecl tc md => some (.typeDecl tc md)

-- Remove only declaration-only locals that are not referenced anywhere else in
-- the same procedure (body/spec/call destinations). This is conservative:
-- we never remove executable statements.
private def pruneUnusedDeclOnlyLocalsInProc (p : Core.Procedure) : Core.Procedure :=
  let usedVars :=
    joinRefs [
      stmtsTouchedVarsExcludingDeclOnly p.body,
      collectVarNamesFromChecks p.spec.preconditions,
      collectVarNamesFromChecks p.spec.postconditions
    ]
  { p with body := p.body.filterMap (pruneUnusedDeclOnlyStmt usedVars) }

private def pruneUnusedDeclOnlyLocals (decls : List Core.Decl) : List Core.Decl :=
  decls.map (fun d =>
    match d with
    | .proc p md => .proc (pruneUnusedDeclOnlyLocalsInProc p) md
    | _ => d)

-- Shared traversal used by both synthetic-helper pruning and BV-cast stub retention.
-- `exprRefs` extracts names from expressions, and `callNameRefs` optionally adds
-- direct procedure-call callee names when needed.
private def exprOpRefsBy (keep : String → Bool) (e : CoreExpr) : List String :=
  ((Lambda.LExpr.getOps e).map CoreIdent.toPretty |>.filter keep).eraseDups

private def collectRefsFromChecks
    (exprRefs : CoreExpr → List String)
    (checks : ListMap CoreLabel Core.Procedure.Check) : List String :=
  joinRefs <| checks.values.map (fun c => exprRefs c.expr)

private partial def stmtRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String) :
    Core.Statement → List String
  | .cmd (.cmd (.init _ _ e _)) => (e.map exprRefs).getD []
  | .cmd (.cmd (.set _ e _)) => exprRefs e
  | .cmd (.cmd (.havoc _ _)) => []
  | .cmd (.cmd (.assert _ e _)) => exprRefs e
  | .cmd (.cmd (.assume _ e _)) => exprRefs e
  | .cmd (.cmd (.cover _ e _)) => exprRefs e
  | .cmd (.call _ f args _) =>
    joinRefs [callNameRefs f, joinRefs <| args.map exprRefs]
  | .block _ ss _ => joinRefs <| ss.map (stmtRefsBy exprRefs callNameRefs)
  | .ite cond t e _ =>
    joinRefs [exprRefs cond, joinRefs (t.map (stmtRefsBy exprRefs callNameRefs)), joinRefs (e.map (stmtRefsBy exprRefs callNameRefs))]
  | .loop guard measure invariant body _ =>
    let measureRefs := match measure with | some m => exprRefs m | none => []
    let invariantRefs := joinRefs <| invariant.map exprRefs
    joinRefs [exprRefs guard, measureRefs, invariantRefs, joinRefs (body.map (stmtRefsBy exprRefs callNameRefs))]
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []

private def stmtsRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String)
    (ss : List Core.Statement) : List String :=
  joinRefs <| ss.map (stmtRefsBy exprRefs callNameRefs)

private def declRefsBy
    (exprRefs : CoreExpr → List String)
    (callNameRefs : String → List String) :
    Core.Decl → List String
  | .func f _ => (f.body.map exprRefs).getD []
  | .recFuncBlock fs _ => joinRefs <| fs.map (fun f => (f.body.map exprRefs).getD [])
  | .proc p _ =>
    joinRefs [collectRefsFromChecks exprRefs p.spec.preconditions,
      collectRefsFromChecks exprRefs p.spec.postconditions,
      stmtsRefsBy exprRefs callNameRefs p.body]
  | .var _ _ e _ => (e.map exprRefs).getD []
  | .ax a _ => exprRefs a.e
  | .distinct _ es _ => joinRefs <| es.map exprRefs
  | .type _ _ => []

-- Collect synthetic helper references from a Core expression.
def exprSyntheticHelperRefs (e : CoreExpr) : List String :=
  exprOpRefsBy isSyntheticHelperName e

private def syntheticHelperCallNameRefs (name : String) : List String :=
  if isSyntheticHelperName name then [name] else []

-- Collect synthetic helper references from a declaration body/spec.
def declSyntheticHelperRefs : Core.Decl → List String :=
  declRefsBy exprSyntheticHelperRefs syntheticHelperCallNameRefs

def isSyntheticHelperDecl : Core.Decl → Bool
  | .func f _ => isSyntheticHelperName (CoreIdent.toPretty f.name)
  | .proc p _ => isSyntheticHelperName (CoreIdent.toPretty p.header.name)
  | _ => false

def declNameString (d : Core.Decl) : String :=
  match d with
  | .recFuncBlock fs _ =>
    if fs.isEmpty then "recFuncBlock__empty"
    else String.intercalate "_" (fs.map (fun f => CoreIdent.toPretty f.name))
  | _ => CoreIdent.toPretty d.name

-- Transitive closure over helper references.
-- `seed` is the initially referenced helper set from normal (non-helper) decls.
-- Performance: O(|helpers|² × |keep|) per iteration with at most |helpers|
-- iterations. Adequate for current Verus tests; switch to HashSet-based
-- worklist if profiling reveals a bottleneck on large codebases.
def closeSyntheticHelperRefs (helperDecls : List Core.Decl) (seed : List String) : List String :=
  -- Adjacency list of the helper dependency graph:
  --   helper name n ↦ direct helper refs in n's body/spec.
  let helperRefs := helperDecls.map (fun d => (declNameString d, declSyntheticHelperRefs d))
  -- `keep` is the currently reachable helper set.
  -- `fuel` is a termination guard to make Lean happy; we usually stop earlier at fixpoint.
  let rec loop (fuel : Nat) (keep : List String) : List String :=
    match fuel with
    | 0 => keep
    | fuel + 1 =>
      let expanded :=
        -- One closure step: for each kept helper n, add n's direct refs.
        helperRefs.foldl (init := keep) (fun acc (n, refs) =>
          if keep.contains n then
            (acc ++ refs).eraseDups
          else
            acc)
      -- Fixpoint reached: no newly reachable helpers.
      if expanded == keep then keep else loop fuel expanded
  -- Start from deduplicated seed helpers.
  loop helperDecls.length seed.eraseDups

-- Drop unreferenced synthetic helper declarations, leaving all non-helper declarations untouched.
def pruneUnreferencedSyntheticHelpers (decls : List Core.Decl) : List Core.Decl :=
  let (helperDecls, nonHelperDecls) := decls.partition isSyntheticHelperDecl
  -- Keep only helper declarations that are actually referenced by retained declarations.
  let seed := joinRefs <| nonHelperDecls.map declSyntheticHelperRefs
  let keep := closeSyntheticHelperRefs helperDecls seed
  decls.filter (fun d =>
    if isSyntheticHelperDecl d then keep.contains (declNameString d) else true)

private def coreDeclTag : Core.Decl → Nat
  -- Defensive: dedup keys include decl kind to avoid collapsing declarations
  -- that share a name but are different kinds (`func` vs `proc`, etc.).
  -- TODO: if Verus/Core guarantee global name uniqueness across kinds, simplify
  -- dedup to name-only keys.
  | .func _ _ => 0
  | .proc _ _ => 1
  | .type _ _ => 2
  | .var _ _ _ _ => 3
  | .ax _ _ => 4
  | .distinct _ _ _ => 5
  | .recFuncBlock _ _ => 6

private def coreDeclScore : Core.Decl → Nat
  | .func f _ => if f.body.isSome then 2 else 1
  | .recFuncBlock fs _ =>
    if fs.any (fun f => f.body.isSome) then 2 else 1
  | .proc p _ =>
    let bodyScore := if p.body.isEmpty then 0 else 2
    let specScore := if p.spec.preconditions.isEmpty && p.spec.postconditions.isEmpty then 0 else 1
    bodyScore + specScore
  | _ => 1

private def sameCoreDeclKey (a b : Core.Decl) : Bool :=
  coreDeclTag a == coreDeclTag b && declNameString a == declNameString b

private def insertCoreDeclDedup (d : Core.Decl) : List Core.Decl → List Core.Decl
  | [] => [d]
  | x :: xs =>
    if sameCoreDeclKey x d then
      if coreDeclScore d > coreDeclScore x then
        d :: xs
      else
        x :: xs
    else
      x :: insertCoreDeclDedup d xs

-- Module shards can repeat imported declarations (often without bodies).
-- Keep one declaration per (kind, name), preferring the richer variant.
def dedupCoreDecls (decls : List Core.Decl) : List Core.Decl :=
  decls.foldl (fun acc d => insertCoreDeclDedup d acc) []

def mkBvToIntCastDecl (w : Nat) (signed : Bool) : Core.Decl :=
  let f : Core.Function :=
    { name := CoreIdent.unres (bvToIntCastName w signed)
      typeArgs := []
      inputs := [(CoreIdent.unres "x", .bitvec w)]
      output := .int
      body := none }
  Core.Decl.func f

def bvToIntCastDecls : List Core.Decl :=
  [1, 8, 16, 32, 64].flatMap (fun w =>
    [mkBvToIntCastDecl w false, mkBvToIntCastDecl w true])

def mkBvToNatCastDecl (w : Nat) (signed : Bool) : Core.Decl :=
  let f : Core.Function :=
    { name := CoreIdent.unres (bvToNatCastName w signed)
      typeArgs := []
      inputs := [(CoreIdent.unres "x", .bitvec w)]
      output := .tcons "nat" []
      body := none }
  Core.Decl.func f

def bvToNatCastDecls : List Core.Decl :=
  [1, 8, 16, 32, 64].flatMap (fun w =>
    [mkBvToNatCastDecl w false, mkBvToNatCastDecl w true])

def mkBvWidenCastDecl (fromW toW : Nat) (signed : Bool) : Core.Decl :=
  let f : Core.Function :=
    { name := CoreIdent.unres (bvWidenCastName fromW toW signed)
      typeArgs := []
      inputs := [(CoreIdent.unres "x", .bitvec fromW)]
      output := .bitvec toW
      body := none }
  Core.Decl.func f

def bvWidenCastDecls : List Core.Decl :=
  supportedBvWidths.flatMap (fun fromW =>
    supportedBvWidths.flatMap (fun toW =>
      if fromW < toW then
        [mkBvWidenCastDecl fromW toW false, mkBvWidenCastDecl fromW toW true]
      else
        []))

private def exprBvToIntCastRefs (e : CoreExpr) : List String :=
  exprOpRefsBy isBvToIntCastName e

private def noCallNameRefs (_name : String) : List String := []

private def declBvToIntCastRefs : Core.Decl → List String
  := declRefsBy exprBvToIntCastRefs noCallNameRefs

private def exprBvWidenCastRefs (e : CoreExpr) : List String :=
  exprOpRefsBy isBvWidenCastName e

private def declBvWidenCastRefs : Core.Decl → List String
  := declRefsBy exprBvWidenCastRefs noCallNameRefs

private def exprBvToNatCastRefs (e : CoreExpr) : List String :=
  exprOpRefsBy isBvToNatCastName e

private def declBvToNatCastRefs : Core.Decl → List String
  := declRefsBy exprBvToNatCastRefs noCallNameRefs

-- Keep cast stubs only when the translated program actually references them.
-- This avoids cluttering Core files that never mix bitvectors and integers.
private def neededBvToNatCastDecls (decls : List Core.Decl) : List Core.Decl :=
  let needed := joinRefs <| decls.map declBvToNatCastRefs
  bvToNatCastDecls.filter (fun d => needed.contains (declNameString d))

private def neededBvToIntCastDecls (decls : List Core.Decl) : List Core.Decl :=
  let needed := joinRefs <| decls.map declBvToIntCastRefs
  bvToIntCastDecls.filter (fun d => needed.contains (declNameString d))

-- Keep width-promotion stubs only when mixed-width bitvector arithmetic/comparisons
-- actually reference them.
private def neededBvWidenCastDecls (decls : List Core.Decl) : List Core.Decl :=
  let needed := joinRefs <| decls.map declBvWidenCastRefs
  bvWidenCastDecls.filter (fun d => needed.contains (declNameString d))

private def natTypeDecl : Core.Decl :=
  Core.Decl.type (.con { name := "nat", params := [] })

/-- Abstract type declarations for Verus stdlib collection types that do not
    already have dedicated emitted preludes or Strata/Core builtins. -/
private def stdlibTypeDecls : List Core.Decl :=
  let oneParam := ["Multiset", "Std_specs_range"]
  let twoParam := ["Verus_Map", "Tuple"]
  let mkOneParam (name : String) : Core.Decl :=
    Core.Decl.type (.con { name := name, params := ["T"] })
  let mkTwoParam (name : String) : Core.Decl :=
    Core.Decl.type (.con { name := name, params := ["T0", "T1"] })
  oneParam.map mkOneParam ++ twoParam.map mkTwoParam

private def tupleStubSignature? (name : String) :
    Option (List String × @Lambda.LMonoTySignature Visibility × LMonoTy) :=
  let t0 : LMonoTy := .ftvar "T0"
  let t1 : LMonoTy := .ftvar "T1"
  let tupleTy : LMonoTy := .tcons "Tuple" [t0, t1]
  match name with
  | "Tuple_ctor_0" => some ([], [], .tcons "Unit" [])
  | "Tuple_ctor_2" =>
      some (["T0", "T1"], [(CoreIdent.unres "x0", t0), (CoreIdent.unres "x1", t1)], tupleTy)
  | "Tuple_2_0" =>
      some (["T0", "T1"], [(CoreIdent.unres "x0", tupleTy)], t0)
  | "Tuple_2_1" =>
      some (["T0", "T1"], [(CoreIdent.unres "x0", tupleTy)], t1)
  | _ => none

/-- Collect `(name, maxArgCount)` pairs for all call sites in Core declarations.
    Tracks procedure calls (explicit arg lists) and expression-level function
    applications (counted by spine length in the `app` chain). -/
private partial def collectExprArity : CoreExpr → Std.HashMap String Nat → Std.HashMap String Nat
  | .app _ fn arg, acc =>
    -- Count spine length: walk left through `app` to find the head and arg count.
    let rec countApps (e : CoreExpr) (n : Nat) : (String × Nat) × CoreExpr :=
      match e with
      | .app _ f _ => countApps f (n + 1)
      | .op _ id _ => ((CoreIdent.toPretty id, n), .const () (.boolConst true))
      -- Only track .op heads for global functions, not .fvar (local variables)
      -- to avoid misclassifying applied higher-order local variables as
      -- missing global functions.
      | .fvar _ _ _ => (("", n), .const () (.boolConst true))
      | other => (("", n), other)
    let ((name, arity), _) := countApps (.app () fn arg) 0
    let acc := if name != "" then
      match acc.get? name with
      | some existing => if arity > existing then acc.insert name arity else acc
      | none => acc.insert name arity
    else acc
    -- Also recurse into subexpressions for nested calls.
    collectExprArity arg (collectExprArity fn acc)
  | .eq _ lhs rhs, acc => collectExprArity rhs (collectExprArity lhs acc)
  | .abs _ _ _ body, acc => collectExprArity body acc
  | .quant _ _ _ _ _ body, acc => collectExprArity body acc
  | .ite _ c t e, acc => collectExprArity e (collectExprArity t (collectExprArity c acc))
  | _, acc => acc

private partial def collectStmtArity : Core.Statement → Std.HashMap String Nat → Std.HashMap String Nat
  | .cmd (.cmd (.init _ _ (some e) _)), acc => collectExprArity e acc
  | .cmd (.cmd (.set _ e _)), acc => collectExprArity e acc
  | .cmd (.cmd (.assert _ e _)), acc => collectExprArity e acc
  | .cmd (.cmd (.assume _ e _)), acc => collectExprArity e acc
  | .cmd (.cmd (.cover _ e _)), acc => collectExprArity e acc
  | .cmd (.call _ f args _), acc =>
    let acc := match acc.get? f with
      | some existing => if args.length > existing then acc.insert f args.length else acc
      | none => acc.insert f args.length
    args.foldl (init := acc) (fun a e => collectExprArity e a)
  | .block _ ss _, acc => ss.foldl (init := acc) (fun a s => collectStmtArity s a)
  | .ite cond t e _, acc =>
    let acc := collectExprArity cond acc
    let acc := t.foldl (init := acc) (fun a s => collectStmtArity s a)
    e.foldl (init := acc) (fun a s => collectStmtArity s a)
  | .loop guard measure invs body _, acc =>
    let acc := collectExprArity guard acc
    let acc := match measure with | some m => collectExprArity m acc | none => acc
    let acc := invs.foldl (init := acc) (fun a e => collectExprArity e a)
    body.foldl (init := acc) (fun a s => collectStmtArity s a)
  | _, acc => acc

/-- Collect procedure names and their max LHS count from `call` statements.
    Names with 0 LHS captures → void procedures (no outputs). -/
private partial def collectCallProcInfo : List Core.Statement → List (String × Nat)
  | [] => []
  | .cmd (.call lhs f _ _) :: rest => (f, lhs.length) :: collectCallProcInfo rest
  | .block _ ss _ :: rest => collectCallProcInfo ss ++ collectCallProcInfo rest
  | .ite _ t e _ :: rest => collectCallProcInfo t ++ collectCallProcInfo e ++ collectCallProcInfo rest
  | .loop _ _ _ body _ :: rest => collectCallProcInfo body ++ collectCallProcInfo rest
  | _ :: rest => collectCallProcInfo rest

/-- Map from procedure name → max LHS capture count. -/
private def collectAllCallProcInfo (decls : List Core.Decl) : Std.HashMap String Nat :=
  let all := decls.flatMap (fun d => match d with
    | .proc p _ => collectCallProcInfo p.body
    | _ => [])
  all.foldl (init := ∅) (fun acc (name, lhsCount) =>
    match acc.get? name with
    | some existing => if lhsCount > existing then acc.insert name lhsCount else acc
    | none => acc.insert name lhsCount)

private def collectRefsWithArity (decls : List Core.Decl) : List (String × Nat) :=
  let acc : Std.HashMap String Nat := ∅
  let acc := decls.foldl (init := acc) (fun acc d => match d with
    | .func f _ => match f.body with
      | some body => collectExprArity body acc
      | none => acc
    | .proc p _ =>
      let acc := (p.spec.preconditions.values ++ p.spec.postconditions.values).foldl
        (init := acc) (fun a c => collectExprArity c.expr a)
      p.body.foldl (init := acc) (fun a s => collectStmtArity s a)
    | .ax a _ => collectExprArity a.e acc
    | _ => acc)
  acc.toList

/-- Collect free type variable names from a monomorphic type. -/
private def collectFtvars : LMonoTy → List String
  | .ftvar n => [n]
  | .tcons _ args => args.flatMap collectFtvars
  | _ => []

/-- Collect type constructor names (e.g. `Seq`, `Tuple`) from a monomorphic type. -/
private def collectTcons : LMonoTy → List String
  | .tcons name args => [name] ++ args.flatMap collectTcons
  | _ => []

private def seqPreludeFallbackTypeDecls : List Core.Decl :=
  seqPreludeOwnedTypeNames.map (fun name => Core.Decl.type (.con { name := name, params := ["T"] }))

private def mkPreludeFallbackFuncDecl? (name : String) : Option Core.Decl := do
  let (params, ret) ← knownPreludeFnSignature? name
  let inputTys := params.map monoTyOfTyp
  let retTy := monoTyOfTyp ret
  let typeArgs := ((inputTys.flatMap collectFtvars) ++ collectFtvars retTy).eraseDups
  let inputs := inputTys.zipIdx.map (fun (ty, i) => (CoreIdent.unres s!"x{i}", ty))
  some <| Core.Decl.func {
    name := CoreIdent.unres name
    typeArgs := typeArgs
    inputs := inputs
    output := retTy
    body := none
  }

private def neededSeqPreludeFallbackDecls
    (_typeRefs opRefs declaredNames : List String) : List Core.Decl :=
  let typeDecls := seqPreludeFallbackTypeDecls.filter (fun d =>
    let name := declNameString d
    !declaredNames.contains name)
  let fnDecls := opRefs.eraseDups.filterMap (fun name =>
    if !isPreludeOwnedValueName name || declaredNames.contains name then
      none
    else
      mkPreludeFallbackFuncDecl? name)
  dedupCoreDecls (typeDecls ++ fnDecls)

/-- Translates VLIR declarations to a Core program, a side map of
    function-name → decreases Core expressions (for the pretty-printer), and a
    flag indicating whether the emitted `.core.st` should prepend the text Seq
    prelude from `prelude/Seq.core.st`. -/
def declsToProgram (decls : List Decl)
    (callSiteTypes : Std.HashMap Ident (List Typ × Typ) := {})
    (useTextSeqPrelude : Bool := true) :
    Except String (Core.Program × Std.HashMap String (List CoreExpr) × Bool) := do
  let noParamFns := collectNoParamFnNamesFromDecls decls
  let projLayouts := buildProjLayouts decls
  let mutArgMap := collectMutArgMapFromDecls decls
  let sfMap := collectSpecFns decls
  let parts ← decls.mapM (declToCore noParamFns projLayouts mutArgMap sfMap decls)
  -- Keep declaration-only procedure stubs unless a stronger reachability proof
  -- is implemented. Some Verus shards reference helpers only through specs,
  -- and dropping them here can lose required declarations.
  let translated := pruneUnreferencedSyntheticHelpers parts.flatten
  let translated := pruneUnusedDeclOnlyLocals translated
  -- Remove `.func` declarations that are shadowed by `recFuncBlock` definitions.
  -- This prevents duplicate declarations when mutual blocks define spec functions.
  let recFuncBlockNames := translated.flatMap (fun d => match d with
    | .recFuncBlock fs _ => fs.map (fun f => CoreIdent.toPretty f.name)
    | _ => [])
  let translated := translated.filter (fun d => match d with
    | .func f _ => !recFuncBlockNames.contains (CoreIdent.toPretty f.name)
    | _ => true)
  -- Only emit stdlib type declarations when referenced in translated signatures.
  let translatedTypeRefs := translated.flatMap (fun d => match d with
    | .func f _ =>
      f.inputs.flatMap (fun (_, ty) => collectTcons ty) ++ collectTcons f.output
    | .proc p _ =>
      p.header.inputs.flatMap (fun (_, ty) => collectTcons ty) ++
      p.header.outputs.flatMap (fun (_, ty) => collectTcons ty)
    | _ => [])
  let neededStdlibTypes := stdlibTypeDecls.filter (fun d =>
    let name := declNameString d
    !isPreludeOwnedTypeName name && translatedTypeRefs.contains name)
  let neededBvToInt := neededBvToIntCastDecls translated
  let neededBvToNat := neededBvToNatCastDecls translated
  let castDecls :=
    [natTypeDecl] ++
    neededStdlibTypes ++
    neededBvToInt ++
    neededBvToNat ++
    neededBvWidenCastDecls translated
  let flat :=
    dedupCoreDecls <| castDecls ++ translated
  -- Auto-stub pass: emit uninterpreted function stubs for referenced-but-
  -- undeclared identifiers (stdlib/pervasive symbols not in the VLIR).
  -- We collect (name, maxArgCount) pairs so stubs have the right arity.
  let allRefsWithArity := collectRefsWithArity flat
  -- Also collect bare identifier references (arity 0) from all ops/fvars.
  let bareRefs := joinRefs <| flat.map (declRefsBy (exprOpRefsBy (fun _ => true)) (fun n => [n]))
  let allRefsWithArity := allRefsWithArity ++ bareRefs.map (fun n => (n, (0 : Nat)))
  -- Collect names introduced by datatype declarations (constructors, testers,
  -- destructors) so we don't emit duplicate stubs for them.
  let datatypeNames := flat.flatMap (fun d => match d with
    | .type (.data ds) _ => ds.flatMap (fun dt =>
      dt.constrs.flatMap (fun c =>
        let ctorName := CoreIdent.toPretty c.name
        let testerName := CoreIdent.toPretty c.testerName
        let fieldNames := c.args.map (fun (f, _) => CoreIdent.toPretty f)
        [ctorName, testerName] ++ fieldNames))
    | _ => [])
  let builtinPrefixes := ["Int.", "Bv1.", "Bv8.", "Bv16.", "Bv32.", "Bv64.",
    "Bool.", "true", "false", "Map.", "__decreases", "Unsupported.",
    "TriggerGroup.", "Triggers."]
  -- Strata Core built-in identifiers that must not be stubbed.
  let strataBuiltins := ["select", "store", "update", "ite"]
  let hasDotDot (n : String) : Bool := (n.splitOn "..").length != 1
  let isBuiltin (n : String) :=
    builtinPrefixes.any (fun p => n.startsWith p) || hasDotDot n ||
    strataBuiltins.contains n
  -- Collect declared names with their arities for comparison.
  let declaredArities : Std.HashMap String Nat := flat.foldl (init := ∅) (fun acc d =>
    match d with
    | .func f _ => acc.insert (CoreIdent.toPretty f.name) f.inputs.length
    | .proc p _ => acc.insert (CoreIdent.toPretty p.header.name) p.header.inputs.length
    | .recFuncBlock fs _ =>
      -- Register all functions in the mutual block as declared
      fs.foldl (init := acc) (fun acc f =>
        acc.insert (CoreIdent.toPretty f.name) f.inputs.length)
    | _ => acc)
  -- A reference needs a stub if: (a) not declared at all, or
  -- (b) declared with 0 params but referenced with >0 args (wrong arity).
  let needsStub (n : String) (arity : Nat) : Bool :=
    if isBuiltin n || isBvToIntCastName n || isBvToNatCastName n ||
       isBvWidenCastName n || isPreludeOwnedTypeName n ||
       isPreludeOwnedValueName n || datatypeNames.contains n then false
    else match declaredArities.get? n with
    | none => true  -- not declared at all
    | some 0 => arity > 0  -- declared with 0 params but called with args
    | _ => false  -- already has correct declaration
  -- Deduplicate by name, keeping the maximum arity for each.
  let refsByName := allRefsWithArity.foldl (init := (∅ : Std.HashMap String Nat))
    (fun acc (n, arity) => match acc.get? n with
      | some existing => if arity > existing then acc.insert n arity else acc
      | none => acc.insert n arity)
  -- Convert Ident-keyed callSiteTypes to Core-sanitized string keys for lookup.
  let callSiteTypesByName : Std.HashMap String (List Typ × Typ) :=
    callSiteTypes.fold (init := ∅) (fun acc ident sig =>
      let key := CoreIdent.toPretty (identToCore ident)
      if acc.contains key then acc else acc.insert key sig)
  let undeclaredWithArity := refsByName.toList.filter (fun (n, arity) => needsStub n arity)
  -- Determine which undeclared symbols are called as procedures (via `call`)
  -- vs used as expression-level functions.
  let procCallInfo := collectAllCallProcInfo flat
  let autoStubs := undeclaredWithArity.flatMap (fun (name, arity) =>
    -- Use type signatures from JSON call sites when available;
    -- fall back to `int` placeholders otherwise.
    let (typeArgs, params, retTy) := match tupleStubSignature? name with
      | some sig => sig
      | none =>
        match callSiteTypesByName.get? name with
        | some (argTypes, retType) =>
          let ps := argTypes.zipIdx.map (fun ((ty : Typ), (i : Nat)) =>
            (CoreIdent.unres s!"x{i}", monoTyOfTyp ty))
          ([], ps, monoTyOfTyp retType)
        | none =>
          let ps := (List.range arity).map (fun i =>
            (CoreIdent.unres s!"x{i}", LMonoTy.int))
          ([], ps, LMonoTy.int)
    match procCallInfo.get? name with
    | some lhsCount =>
      -- Emit a procedure stub for `call` targets.
      let outputs : @Lambda.LMonoTySignature Visibility :=
        if lhsCount > 0 then [(CoreIdent.unres "_ret", retTy)] else []
      [Core.Decl.proc {
        header := { name := CoreIdent.unres name, typeArgs := typeArgs,
                     inputs := params, outputs := outputs }
        spec := { modifies := [], preconditions := [], postconditions := [] }
        body := []
      }]
    | none =>
      -- Emit a function stub for expression-level references.
      [Core.Decl.func {
        name := CoreIdent.unres name
        typeArgs := typeArgs
        inputs := params
        output := retTy
        body := none
      }])
  -- Collect free type variables from auto-stubs and emit `type X;`
  -- declarations for any that aren't already declared.
  let stubFtvars := autoStubs.flatMap (fun d => match d with
    | .func f _ =>
      let inputFtvars := f.inputs.flatMap (fun (_, ty) => collectFtvars ty)
      let outputFtvars := collectFtvars f.output
      (inputFtvars ++ outputFtvars).filter (fun n => !f.typeArgs.contains n)
    | .proc p _ =>
      let inputFtvars := p.header.inputs.flatMap (fun (_, ty) => collectFtvars ty)
      let outputFtvars := p.header.outputs.flatMap (fun (_, ty) => collectFtvars ty)
      (inputFtvars ++ outputFtvars).filter (fun n => !p.header.typeArgs.contains n)
    | _ => []) |>.eraseDups
  let stubTcons := autoStubs.flatMap (fun d => match d with
    | .func f _ =>
      let inputTcons := f.inputs.flatMap (fun (_, ty) => collectTcons ty)
      let outputTcons := collectTcons f.output
      inputTcons ++ outputTcons
    | .proc p _ =>
      let inputTcons := p.header.inputs.flatMap (fun (_, ty) => collectTcons ty)
      let outputTcons := p.header.outputs.flatMap (fun (_, ty) => collectTcons ty)
      inputTcons ++ outputTcons
    | _ => []) |>.eraseDups
  -- Collect already-declared type names (from type decls and datatype decls).
  let declaredTypeNames := flat.flatMap (fun d => match d with
    | .type (.con c) _ => [c.name]
    | .type (.data ds) _ => ds.map (·.name)
    | _ => [])
  let knownTypeNames := declaredTypeNames ++ stdlibTypeDecls.map declNameString ++ ["nat", "int", "bool", "string", "bitvec"]
  let neededAutoStubStdlibTypes := stdlibTypeDecls.filter (fun d =>
    let name := declNameString d
    stubTcons.contains name && !declaredTypeNames.contains name)
  let freeTypeVarDecls := stubFtvars.filter (fun n => !knownTypeNames.contains n)
    |>.map (fun name => Core.Decl.type (.con { name := name, params := [] }))
  -- Remove 0-arity declarations that are being replaced by auto-stubs
  -- with correct arities.
  let autoStubNameSet : Std.HashSet String := autoStubs.foldl (init := ∅)
    (fun acc d => acc.insert (declNameString d))
  let flat := flat.filter (fun d => !autoStubNameSet.contains (declNameString d))
  let (typeDecls, otherDecls) := flat.partition (fun d => match d with | .type _ _ => true | _ => false)
  -- Add missing type declarations introduced by auto-stubs.
  let typeDecls := typeDecls ++ neededAutoStubStdlibTypes ++ freeTypeVarDecls
  -- Place auto-stubs BEFORE other declarations so Strata's sequential
  -- parser can resolve forward references to stdlib/pervasive symbols.
  let otherDecls := autoStubs ++ otherDecls
  -- Build a side map of function-name → decreases comment string from the
  -- VLIR SpecFn.decreases field.  This avoids polluting Core's semantic
  -- `Func.axioms`.  We extract `decrease%init*` RHS expressions from
  -- each spec function's termination-check body.
  let fnDecEntries ← sfMap.toArray.toList.filterMapM (fun (name, sf) => do
    match sf.decreases with
    | some decStm =>
      let decExps := collectDecreasesExps decStm
      if !decExps.isEmpty then
        let env := addNoParamFnMarkers (envFromDecls sf.inputs) noParamFns
        let coreExprs ← decExps.mapM (expToCore env none)
        let fnStr := CoreIdent.toPretty (identToCore name)
        pure (some (fnStr, coreExprs))
      else
        pure none
    | none => pure none)
  let fnDecMap := fnDecEntries.foldl (init := (∅ : Std.HashMap String (List CoreExpr)))
    (fun acc (k, v) => acc.insert k v)
  let decls0 := typeDecls ++ otherDecls
  let finalTypeRefs := decls0.flatMap (fun d => match d with
    | .func f _ =>
      f.inputs.flatMap (fun (_, ty) => collectTcons ty) ++ collectTcons f.output
    | .proc p _ =>
      p.header.inputs.flatMap (fun (_, ty) => collectTcons ty) ++
      p.header.outputs.flatMap (fun (_, ty) => collectTcons ty)
    | _ => [])
  let finalOpRefs :=
    joinRefs <| decls0.map (declRefsBy (exprOpRefsBy (fun _ => true)) (fun n => [n]))
  let seqPreludeNeeded := needsSeqPrelude finalTypeRefs finalOpRefs
  let seqPreludeFallbackDecls :=
    if seqPreludeNeeded && !useTextSeqPrelude then
      neededSeqPreludeFallbackDecls finalTypeRefs finalOpRefs (decls0.map declNameString)
    else
      []
  let decls1 :=
    if seqPreludeFallbackDecls.isEmpty then decls0 else dedupCoreDecls (seqPreludeFallbackDecls ++ decls0)
  let finalDecls :=
    if seqPreludeNeeded && useTextSeqPrelude then
      decls0.filter (fun d =>
        declNameString d != "nat" && !isSeqPreludeProvidedCastName (declNameString d))
    else
      decls1
  return ({ decls := finalDecls }, fnDecMap, seqPreludeNeeded)


/-! ## Strata Core pretty-printer (temp) -/
namespace Pretty

mutual
partial def monoTyToString : LMonoTy → String
  | .tcons "bool" [] => "bool"
  | .tcons "int" [] => "int"
  | .tcons "string" [] => "string"
  | .bitvec n => s!"bv{n}"
  | .ftvar n => n
  | .tcons "arrow" [arg, res] =>
    s!"{monoTyArgToString arg} -> {monoTyToString res}"
  | .tcons name [] => name
  | .tcons name args =>
    let argsStr := String.intercalate " " (args.map monoTyArgToString)
    s!"{name} {argsStr}"

partial def monoTyArgToString : LMonoTy → String
  | t@(.tcons _ (_ :: _)) => s!"({monoTyToString t})"
  | t => monoTyToString t
end

def tyToString (ty : LTy) : String :=
  match ty with
  | .forAll _ mty => monoTyToString mty

partial def exprToString (e : CoreExpr) : String :=
  exprToStringWithBound [] e
where
  ppIdent (id : CoreIdent) : String :=
    -- Core AST identifiers are already normalized at construction sites.
    -- Re-sanitizing here can corrupt builtins (e.g. `Int.Sub` -> `Int_Sub`).
    CoreIdent.toPretty id

  constToString : LConst → String
  | .intConst i => toString i
  | .boolConst b => if b then "true" else "false"
  | .strConst s => s!"\"{s}\""
  | .realConst r => toString r
  | .bitvecConst n b => "bv{" ++ toString n ++ "}(" ++ toString b.toNat ++ ")"

  collectApps : CoreExpr → CoreExpr × List CoreExpr
  | .app _ fn arg =>
    let (h, args) := collectApps fn
    (h, args ++ [arg])
  | e => (e, [])

  callString (name : String) (args : List String) : String :=
    s!"{name}({String.intercalate ", " args})"

  bvUnaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "Not" => some "~"
      | some "Neg" => some "-"
      | _ => none
    else
      none

  bvBinaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "Add" => some "+"
      | some "Sub" => some "-"
      | some "Mul" => some "*"
      | some "And" => some "&"
      | some "Or" => some "|"
      | some "Xor" => some "^"
      | some "Shl" => some "<<"
      | some "UShr" => some ">>"
      | some "SShr" => some ">>s"
      | some "UDiv" => some "div"
      | some "UMod" => some "mod"
      | some "SDiv" => some "sdiv"
      | some "SMod" => some "smod"
      | some "ULt" => some "<"
      | some "ULe" => some "<="
      | some "UGt" => some ">"
      | some "UGe" => some ">="
      | some "SLt" => some "<s"
      | some "SLe" => some "<=s"
      | some "SGt" => some ">s"
      | some "SGe" => some ">=s"
      | _ => none
    else
      none

  getBound? (bound : List String) (idx : Nat) : Option String :=
    let rec go (i : Nat) (rest : List String) : Option String :=
      match rest with
      | [] => none
      | x :: xs => if i == idx then some x else go (i + 1) xs
    go 0 bound

  -- Collect a maximal chain of same-kind quantifiers so we can print:
  --   forall x: T, y: U :: { trig } body
  -- instead of nested:
  --   forall x: T :: forall y: U :: body
  --
  -- `boundAcc` mirrors the bound-variable environment used for body printing.
  -- As we descend quantifiers, new binders are cons'ed to the front.
  -- Returns (binders, bound', triggerExpr, body) where triggerExpr is from the
  -- innermost quantifier in the chain.
  collectQuantChain
      (k : Lambda.QuantifierKind)
      (boundAcc : List String)
      (e : CoreExpr) :
      (List (String × Option String) × List String × CoreExpr × CoreExpr) :=
    let rec go (boundNow : List String) (acc : List (String × Option String))
        (lastTrig : CoreExpr) (cur : CoreExpr) :
        (List (String × Option String) × List String × CoreExpr × CoreExpr) :=
      match cur with
      | .quant _ k' name ty trig body =>
        if k' == k then
          let binderName := if name.isEmpty then s!"x{boundNow.length}" else name
          let tyStr := ty.map (fun mty => tyToString (.forAll [] mty))
          go (binderName :: boundNow) (acc ++ [(binderName, tyStr)]) trig body
        else
          (acc, boundNow, lastTrig, cur)
      | _ => (acc, boundNow, lastTrig, cur)
    go boundAcc [] (LExpr.noTrigger ()) e

  -- Decode the trigger tree produced by `Core.mkTriggerExpr`.  The encoding
  -- uses Strata's official ops: `Triggers.addGroup`, `TriggerGroup.addTrigger`,
  -- `Triggers.empty`, `TriggerGroup.empty`.
  --
  -- We mirror the logic of `extractTriggerPatterns` from Strata's ASTtoCST but
  -- render each expression as text via our local `exprToStringWithBound`.
  decodeTriggerTree (bound : List String) (e : CoreExpr) : List String :=
    match e with
    | .bvar _ 0 => []  -- noTrigger sentinel
    | .app _ (.app _ (.op _ name _) arg) rest =>
      match name.name with
      | "TriggerGroup.addTrigger" =>
        exprToStringWithBound bound arg :: decodeTriggerTree bound rest
      | "Triggers.addGroup" =>
        decodeTriggerTree bound arg ++ decodeTriggerTree bound rest
      | _ => []  -- unknown op
    | .op _ name _ =>
      if name.name == "TriggerGroup.empty" || name.name == "Triggers.empty"
      then []
      else []
    | _ => []

  -- Render the trigger slot of the innermost quantifier to textual trigger
  -- groups like `{ f(x0), g(x0, x1) }`.
  -- Returns the empty string when there are no triggers.
  triggerGroupsStr (bound : List String) (trigExpr : CoreExpr) : String :=
    match trigExpr with
    | .bvar _ 0 => ""  -- noTrigger
    | _ =>
      let exprs := decodeTriggerTree bound trigExpr
      if exprs.isEmpty then ""
      else
        s!" \{ {String.intercalate ", " exprs} }\n  "

  exprToStringWithBound (bound : List String) (e : CoreExpr) : String :=
    match e with
    | .const _ c => constToString c
    | .fvar _ id _ => ppIdent id
    | .op _ id _ => ppIdent id
    | .bvar _ idx =>
      match getBound? bound idx with
      | some name => name
      | none => s!"_b{idx}"
    | .eq _ a b => s!"({exprToStringWithBound bound a} == {exprToStringWithBound bound b})"
    | .ite _ c t f =>
      s!"(if {exprToStringWithBound bound c} then {exprToStringWithBound bound t} \
else {exprToStringWithBound bound f})"
    | .quant _ k _ _ _ _ =>
      let kw := match k with
        | .all => "forall"
        | .exist => "exists"
      let (binders, bound', trigExpr, body) := collectQuantChain k bound e
      let binderStrs := binders.map (fun (name, tyStr) =>
        match tyStr with
        | some ts => s!"{name}: {ts}"
        | none => name)
      let trigStr := triggerGroupsStr bound' trigExpr
      s!"{kw} {String.intercalate ", " binderStrs} ::{trigStr} {exprToStringWithBound bound' body}"
    | .abs _ _ _ _ =>
      -- Core textual syntax in this pipeline is first-order; lambda abstractions
      -- are currently emitted as an explicit placeholder symbol to avoid
      -- unparsable Lean-format output.
      "Unsupported.lambda"
    | .app _ _ _ =>
      let (head, args) := collectApps e
      match head, args with
      | .op _ id _, [a] =>
        match ppIdent id with
        | "Bool.Not" => s!"(!{exprToStringWithBound bound a})"
        | "Int.Neg" => s!"(-{exprToStringWithBound bound a})"
        | op =>
          match bvUnaryOp? op with
          | some sym => s!"({sym}{exprToStringWithBound bound a})"
          | none => callString op [exprToStringWithBound bound a]
      | .op _ id _, [a, b] =>
        let op := ppIdent id
        let lhs := exprToStringWithBound bound a
        let rhs := exprToStringWithBound bound b
        match op with
        | "Map.Select" => s!"({lhs}[{rhs}])"
        | "select" => s!"({lhs}[{rhs}])"
        | "Int.Add" => s!"({lhs} + {rhs})"
        | "Int.Sub" => s!"({lhs} - {rhs})"
        | "Int.Mul" => s!"({lhs} * {rhs})"
        | "Int.Div" => s!"({lhs} div {rhs})"
        | "Int.Mod" => s!"({lhs} mod {rhs})"
        | "Int.Lt" => s!"({lhs} < {rhs})"
        | "Int.Le" => s!"({lhs} <= {rhs})"
        | "Int.Gt" => s!"({lhs} > {rhs})"
        | "Int.Ge" => s!"({lhs} >= {rhs})"
        | "Bool.And" => s!"({lhs} && {rhs})"
        | "Bool.Or" => s!"({lhs} || {rhs})"
        | "Bool.Implies" => s!"({lhs} ==> {rhs})"
        | "Bool.Equiv" => s!"({lhs} == {rhs})"
        | _ =>
          match bvBinaryOp? op with
          | some sym => s!"({lhs} {sym} {rhs})"
          | none => callString op [lhs, rhs]
      | .op _ id _, [a, b, c] =>
        let op := ppIdent id
        let lhs := exprToStringWithBound bound a
        let idx := exprToStringWithBound bound b
        let val := exprToStringWithBound bound c
        match op with
        | "Map.Update" => s!"({lhs}[{idx} := {val}])"
        | "update" => s!"({lhs}[{idx} := {val}])"
        | _ => callString op [lhs, idx, val]
      | .op _ id _, _ =>
        callString (ppIdent id) (args.map (exprToStringWithBound bound))
      | .fvar _ id _, _ =>
        callString (ppIdent id) (args.map (exprToStringWithBound bound))
      | .bvar _ _, _ =>
        callString (exprToStringWithBound bound head) (args.map (exprToStringWithBound bound))
      | _, _ =>
        -- Keep unsupported expression forms explicit and machine-searchable in
        -- emitted Core text (consistent with other placeholders).
        "Unsupported.expr"

def indentString (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

mutual
partial def stmtsToLines (indent : Nat) (ss : List Core.Statement) : List String :=
  match ss with
  | [] => []
  -- Merge `ret := expr; // return` into `// return expr`
  | .cmd (.cmd (.set _name e _)) :: .cmd (.cmd (.assume "__return__" _ _)) :: rest =>
    let pad := indentString indent
    [s!"{pad}// return {exprToString e};"] ++ stmtsToLines indent rest
  | s :: rest => stmtToLines indent s ++ stmtsToLines indent rest

partial def stmtToLines (indent : Nat) (s : Core.Statement) : List String :=
  let pad := indentString indent
  match s with
  | .cmd (.cmd (.init name ty e _)) =>
    let n := CoreIdent.toPretty name
    match e with
    | none =>
      [s!"{pad}var {n} : {tyToString ty};"]
    | some rhs =>
      if isDeclSentinel rhs then
        [s!"{pad}var {n} : {tyToString ty};"]
      else
        [s!"{pad}var {n} : {tyToString ty} := {exprToString rhs};"]
  | .cmd (.cmd (.set name e _)) =>
    [s!"{pad}{CoreIdent.toPretty name} := {exprToString e};"]
  | .cmd (.cmd (.havoc name _)) =>
    [s!"{pad}havoc {CoreIdent.toPretty name};"]
  | .cmd (.cmd (.assert label e _)) =>
    if label.isEmpty then
      [s!"{pad}assert {exprToString e};"]
    else
      [s!"{pad}assert [{label}]: {exprToString e};"]
  | .cmd (.cmd (.assume label e _)) =>
    if label == "__return__" then
      [s!"{pad}// return;"]
    else if label.isEmpty then
      [s!"{pad}assume {exprToString e};"]
    else
      [s!"{pad}assume [{label}]: {exprToString e};"]
  | .cmd (.cmd (.cover label e _)) =>
    if label.isEmpty then
      [s!"{pad}cover {exprToString e};"]
    else
      [s!"{pad}cover [{label}]: {exprToString e};"]
  | .cmd (.call lhs pname args _) =>
    let lhsStr :=
      if lhs.isEmpty then ""
      else s!"{String.intercalate ", " (lhs.map CoreIdent.toPretty)} := "
    let argsStr := String.intercalate ", " (args.map exprToString)
    [s!"{pad}call {lhsStr}{pname}({argsStr});"]
  | .block lbl ss _ =>
    let body := stmtsToLines (indent + 1) ss
    if lbl.isEmpty then
      [pad ++ "{"] ++ body ++ [pad ++ "}"]
    else
      [s!"{pad}{lbl}:", pad ++ "{"] ++ body ++ [pad ++ "}"]
  | .ite cond t e _ =>
    let head := s!"{pad}if ({exprToString cond}) " ++ "{"
    let thenLines := stmtsToLines (indent + 1) t
    if e.isEmpty then
      [head] ++ thenLines ++ [pad ++ "}"]
    else
      let elseLines := stmtsToLines (indent + 1) e
      [head] ++ thenLines ++ [pad ++ "} else {"] ++ elseLines ++ [pad ++ "}"]
  | .loop guard measure invs body _ =>
    let measureLine := match measure with
      | some m => [s!"{pad}  decreases {exprToString m}"]
      | none => []
    let invLine := invs.map (fun i => s!"{pad}  invariant {exprToString i}")
    let head := s!"{pad}while ({exprToString guard})"
    let bodyLines := stmtsToLines (indent + 1) body
    [head] ++ measureLine ++ invLine ++ [pad ++ "{"] ++ bodyLines ++ [pad ++ "}"]
  | .exit lbl _ =>
    match lbl with
    | some l => [s!"{pad}exit {l};"]
    | none => [s!"{pad}exit;"]
  | .funcDecl _ _ =>
    -- Current VLIR→Core lowering path does not emit statement-level function declarations.
    [s!"{pad}/* unsupported: statement-level function declaration */"]
  | .typeDecl _ _ =>
    [s!"{pad}/* unsupported: statement-level type declaration */"]
end

def typeArgsToString (args : List String) : String :=
  if args.isEmpty then "" else s!"<{String.intercalate ", " args}>"

def typeParamsToString (num : Nat) : String :=
  if num == 0 then
    ""
  else
    let names := (List.range num).map (fun i => s!"T{i}")
    let binds := names.map (fun n => s!"{n}: Type")
    s!" ({String.intercalate ", " binds})"

def datatypeTypeArgsToString (args : List String) : String :=
  if args.isEmpty then
    "()"
  else
    let binds := args.map (fun n => s!"{sanitizeIdent n}: Type")
    "(" ++ String.intercalate ", " binds ++ ")"

def datatypeConstrToString (c : LConstr Visibility) : String :=
  let fields :=
    c.args.map (fun (field, ty) =>
      s!"{CoreIdent.toPretty field}: {tyToString (.forAll [] ty)}")
  s!"{CoreIdent.toPretty c.name}({String.intercalate ", " fields})"

def datatypeDeclToString (d : LDatatype Visibility) : String :=
  let ctors := String.intercalate ", " (d.constrs.map datatypeConstrToString)
  "datatype " ++ d.name ++ " " ++ datatypeTypeArgsToString d.typeArgs ++ " { " ++ ctors ++ " };"

def procToString (p : Core.Procedure) : String :=
  let inputs := sigToString p.header.inputs
  let outputs := sigToString p.header.outputs
  let header :=
    s!"procedure {CoreIdent.toPretty p.header.name}{typeArgsToString p.header.typeArgs}({inputs}) returns ({outputs})"
  -- Extract `__decreases__` sentinels from the body and render in the spec block.
  let (decreasesStmts, bodyStmts) := p.body.partition (fun s =>
    match s with
    | .cmd (.cmd (.assume label _ _)) => label == "__decreases__"
    | _ => false)
  let decreasesLines := decreasesStmts.filterMap (fun s =>
    match s with
    | .cmd (.cmd (.assume _ e _)) =>
      let inner := exprToString e
      let args := inner.dropWhile (· != '(')
      some s!"  // decreases {args}"
    | _ => none)
  let specLines :=
    (p.spec.modifies.map (fun v => s!"  modifies {CoreIdent.toPretty v};"))
    ++ (p.spec.preconditions.map (fun (_, c) => s!"  requires ({exprToString c.expr});"))
    ++ (p.spec.postconditions.map (fun (_, c) => s!"  ensures ({exprToString c.expr});"))
    ++ decreasesLines
  let specBlock :=
    if specLines.isEmpty then
      []
    else
      ["spec {"] ++ specLines ++ ["}"]
  let bodyLines := stmtsToLines 1 bodyStmts
  let body := ["{"] ++ bodyLines ++ ["};"]
  String.intercalate "\n" ([header] ++ specBlock ++ body)
where
  sigToString (sig : @Lambda.LMonoTySignature Visibility) : String :=
    String.intercalate ", " (sig.map (fun (id, ty) =>
      s!"{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))

def funcToString (f : Core.Function) (fnDecreasesMap : Std.HashMap String (List CoreExpr) := ∅) : String :=
  -- `@[cases]` comes from the function attributes
  let recCasesIdx? :=
    if f.body.isSome then
      Strata.DL.Util.FuncAttr.findInlineIfConstr f.attr
    else
      none
  let inputs := String.intercalate ", " (f.inputs.zipIdx.map (fun ((id, ty), i) =>
    let ann := if recCasesIdx? == some i then "@[cases] " else ""
    s!"{ann}{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))
  let header := s!"function {CoreIdent.toPretty f.name}{typeArgsToString f.typeArgs}({inputs}): {tyToString (.forAll [] f.output)}"
  let decComment := match fnDecreasesMap.get? (CoreIdent.toPretty f.name) with
    | some exprs =>
      let exprsStr := String.intercalate ", " (exprs.map exprToString)
      s!"\n    // decreases ({exprsStr})"
    | none => ""
  match f.body with
  | none => header ++ ";" ++ decComment
  | some body =>
    let bodyStr := exprToString body
    if decComment.isEmpty then
      String.intercalate "\n" [header ++ " {", "  " ++ bodyStr, "}"]
    else
      -- Put `{` on a new line so the `// decreases` comment doesn't swallow it.
      String.intercalate "\n" [header ++ decComment, "{", "  " ++ bodyStr, "}"]

private def recFuncBlockToString (fs : List Core.Function)
    (fnDecreasesMap : Std.HashMap String (List CoreExpr) := ∅) : String :=
  match fs with
  | [] => ""
  | _ =>
    let rendered := fs.map (fun f => funcToString { f with isRecursive := false } fnDecreasesMap)
    "rec " ++ String.intercalate "\n" rendered ++ ";"

def declToString (d : Core.Decl) (fnDecreasesMap : Std.HashMap String (List CoreExpr) := ∅) : String :=
  match d with
  | .proc p _ => procToString p
  | .func f _ =>
    if f.isRecursive && f.body.isSome then
      recFuncBlockToString [f] fnDecreasesMap
    else
      funcToString f fnDecreasesMap
  | .recFuncBlock fs _ => recFuncBlockToString fs fnDecreasesMap
  | .type t _ =>
    match t with
    | .con c => s!"type {c.name}{typeParamsToString c.numargs};"
    | .syn s => s!"type {s.name} := {tyToString (.forAll [] s.type)};"
    | .data ds => String.intercalate "\n" (ds.map datatypeDeclToString)
  | .ax a _ => s!"axiom {CoreIdent.toPretty a.name}: {exprToString a.e};"
  | .var name ty e _ =>
    match e with
    | some rhs => s!"var {CoreIdent.toPretty name} : {tyToString ty} := {exprToString rhs};"
    | none => s!"var {CoreIdent.toPretty name} : {tyToString ty};"
  | .distinct lbl es _ =>
    let esStr := String.intercalate ", " (es.map exprToString)
    s!"distinct [{lbl}] {esStr};"

def programToString (p : Core.Program) (fnDecreasesMap : Std.HashMap String (List CoreExpr) := ∅) : String :=
  let decls := p.decls.map (declToString · fnDecreasesMap)
  let body := String.intercalate "\n\n" decls
  if body.isEmpty then
    "program Core;\n"
  else
    "program Core;\n\n" ++ body ++ "\n"

end Pretty

def declsToCoreString (decls : List Decl) : Except String String := do
  let (p, fnDecMap, _) ← declsToProgram decls
  return Pretty.programToString p fnDecMap

end ToCore

end VerusLean
