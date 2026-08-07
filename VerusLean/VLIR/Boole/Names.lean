/-
  Boole.Names — source-name normalization and recognized library-name shapes.

  The translator receives Verus/VLIR identifiers with Rust paths, generated
  impl-block fragments, and names that may collide with Boole keywords.  This
  module centralizes the syntactic name policy used before BooleDDM lowering.
-/
import VerusLean.VLIR.Defs

namespace VerusLean.Boole.Names

open VerusLean

/-- Boole/Core reserved keywords that are also valid Rust identifiers, so a
    source name spelled like one collides with the grammar (e.g. a local named
    `out` clashes with the `out`/`inout` call-argument modifiers, a type named
    `type` with the `type` keyword).  Such names are suffixed with `_` on
    emission.  Extend as further collisions surface. -/
def strataReservedIdents : List String :=
  ["type", "out", "inout"]

/-- Sanitize an identifier for Boole emission.
    First char: [A-Za-z_], rest: [A-Za-z0-9_'?!].
    Characters outside this set are replaced by `_`, and a name that lands on a
    reserved keyword is suffixed with `_`. -/
def sanitizeIdent (s : String) : String :=
  match s.toList with
  | [] => "_"
  | c :: cs =>
    let first := if c.isAlpha || c == '_' then c else '_'
    let rest := cs.map (fun c =>
      if c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!' then c else '_')
    let ident := String.ofList (first :: rest)
    if strataReservedIdents.contains ident then ident ++ "_" else ident

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

/-! ## Support Tuple Datatype Names

The binary tuple support datatype is emitted as `Tuple2`: cvc5 reserves
`Tuple` as a builtin sort, so a user-declared `(declare-datatype Tuple
(par …))` is shadowed at SMT parsing and applications of its selectors fail
to type-match ("matching failed for selector argument of parameterized
datatype").  Parsed user datatype names are decapitalized
(`pathedNameFromJson`), so a capitalized support name cannot collide with a
user type. -/

def tupleTypeName : String := "Tuple2"

def tupleCtorName : String := s!"{tupleTypeName}_ctor_2"

def tupleFstSelector : String := s!"{tupleTypeName}.._0"

def tupleSndSelector : String := s!"{tupleTypeName}.._1"

def unitTypeName : String := "Unit"

def unitCtorName : String := "Unit_unit"

/-! ## Datatype and Field Names -/

private def strataReservedTypeNames : List String :=
  ["Seq", "Set", "Map", "Multiset", "Triggers", "TriggerGroup"]

private def canonicalStdlibTypeName? (dt : Ident) : Option String :=
  let raw := dt.toString
  let rawLower := raw.toLower
  let short := sanitizeIdent (stripLeadingNamespace raw)
  if rawLower.contains "vstd" then
    if short == "Seq" && rawLower.contains "seq" then some "Seq"
    else if short == "Set" && rawLower.contains "set" then some "Set"
    else if short == "Map" && rawLower.contains "map" then some "Map"
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
  let dtName := datatypeNameOf dt
  let variantName := sanitizeIdent variant
  -- A variant named like its datatype is a plain (single-variant) struct,
  -- whose declaration binds fields by their own names (`fieldAccessorNameOf`:
  -- named fields stay bare, positional fields become `_<i>`).  Only true enum
  -- variants need the `<dt>_<variant>_` disambiguation prefix; enum
  -- declarations bind their fields through this same function, so both sides
  -- agree either way.
  let isStructVariant := variantName.toLower == dtName.toLower
  if field == "_" then
    s!"{dtName}_{variantName}_0"
  else
    match field.toNat? with
    | some i =>
      if isStructVariant then field else s!"{dtName}_{variantName}_{i}"
    | none =>
      if isStructVariant then field
      else s!"{dtName}_{variantName}_{sanitizeIdent field}"

/-! ## Recognized Library Name Shapes -/

def isVecTypeName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "Vec" || s.endsWith "vec"

/-- The Rust global allocator type (`alloc::alloc::Global`) — the `A` type
    parameter of `Vec`/`Box`.  It is a verification phantom: the translator
    erases it (a `Vec` lowers to `Sequence`, dropping its allocator arg), so no
    emitted Boole type ever names it.  Keyed on the lowered datatype name, which
    is exactly what an opaque emission would declare. -/
def isAllocatorTypeName (name : Ident) : Bool :=
  datatypeNameOf name == "Alloc_global"

def isVecLenSpecName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "spec_vec_len"

def isSeqLenSpecName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "Seq.len" || s.endsWith "seq.len"

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

/-- Recognize `vstd::prelude::cloned` (ghost predicate asserting that the
    second argument is a clone of the first). For every `Clone` impl Verus
    admits, cloning is deterministic, so `cloned(x, y)` reduces to
    `x == y`. Matching on the name lets the translator rewrite without
    needing a prelude definition. -/
def isClonedName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "::cloned" || s.endsWith ".cloned" || s == "cloned"

/-- vstd's `arbitrary()`, an unspecified value of the return type.  See
    `exprIsBareArbitrary`. -/
def isPervasiveArbitraryName (name : Ident) : Bool :=
  identToBoole name == "Pervasive_arbitrary"

/-- Boole name of vstd's `low_bits_mask`.  The fn is uninterpreted; ground
    axioms supply its value at literal exponents (`lowBitsMaskValAxioms`). -/
def lowBitsMaskBooleName : String := "Bits_low_bits_mask"

def isLowBitsMaskName (name : Ident) : Bool :=
  identToBoole name == lowBitsMaskBooleName

def isBoxNewName (name : Ident) : Bool :=
  identToBoole name == "Boxed_box_new"

def isArrayAsSliceName (name : Ident) : Bool :=
  identToBoole name == "Array_array_as_slice"

def isArrayIndexGetName (name : Ident) : Bool :=
  identToBoole name == "Array_array_index_get"

def isArrayFillForCopyTypesName (name : Ident) : Bool :=
  identToBoole name == "Array_array_fill_for_copy_types"

/-- Recognize `core::num::<impl uN>::wrapping_add` for any integer width.
    Verus emits one impl-block per integer width (`impl&%N`); after
    `identToBoole` they all canonicalize to `Num_wrapping_add`. -/
def isWrappingAddName (name : Ident) : Bool :=
  identToBoole name == "Num_wrapping_add"

def isSliceLenSpecName (name : Ident) : Bool :=
  identToBoole name == "Slice_spec_slice_len"

def isSliceLenExecName (name : Ident) : Bool :=
  identToBoole name == "Slice_len"

def isSliceIndexGetName (name : Ident) : Bool :=
  identToBoole name == "Slice_slice_index_get"

def isSliceIntoVecName (name : Ident) : Bool :=
  identToBoole name == "Slice_into_vec"

def isVecFromElemExecName (name : Ident) : Bool :=
  identToBoole name == "Vec_from_elem"

def isVecPushExecName (name : Ident) : Bool :=
  identToBoole name == "Vec_push"

/-- `Vec::new()` — a compiler intrinsic with no exported Verus declaration.
    With `Vec := Sequence` it constructs the empty sequence. -/
def isVecNewExecName (name : Ident) : Bool :=
  identToBoole name == "Vec_new"

/-- `Vec::with_capacity(n)` — like `Vec::new()`, produces an empty vector;
    the capacity hint does not affect the (zero) length. -/
def isVecWithCapacityExecName (name : Ident) : Bool :=
  identToBoole name == "Vec_with_capacity"

def isIndexSetName (name : Ident) : Bool :=
  identToBoole name == "Std_specs_Core_index_set"

/-- `v[i] = value` on an owned local `Vec` compiles to this call rather than to
    `index_set`.  It returns a mutable reference to the element, which the
    program then writes through; `Normalize.inlineVecIndexMutWrites` folds that
    back into a single three-argument call. -/
def isVecIndexMutExecName (name : Ident) : Bool :=
  identToBoole name == "Std_specs_Vec_vec_index_mut"

/-- `vec2seq` branch: call targets that should be dropped during
    translation because the Vec surface collapses to `Sequence.*` ops.
    `Vec_from_elem` is the one kept stub (we synthesize a body for it);
    operations such as `Vec_push` that have direct statement lowerings are
    handled before this fallback.  Any remaining `Vec_*` or `Slice_into_vec`
    call is a dead procedure with no Boole-side counterpart. -/
def isVec2SeqDroppedCalleeName (name : Ident) : Bool :=
  let n := identToBoole name
  (n.startsWith "Vec_" && n != "Vec_from_elem") || isSliceIntoVecName name

/-- Recognize the exec-side `Clone::clone` method. Every `Clone` impl
    Verus accepts is deterministic, and our spec-level `Sequence` is
    value-typed, so `y := clone(x)` collapses to the direct assignment
    `y := x`. Inlining at the call site also lets us drop the stub
    `Clone_Clone_clone` procedure decl entirely — it otherwise emits an
    empty-spec empty-body procedure whose return is effectively havoc'd
    (unlike `Boxed_box_new`, which carries `ensures result == x`). -/
def isCloneExecName (name : Ident) : Bool :=
  identToBoole name == "Clone_Clone_clone"

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

end VerusLean.Boole.Names
