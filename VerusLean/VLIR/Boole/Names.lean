/-
  Boole.Names — source-name normalization and recognized library-name shapes.

  The translator receives Verus/VLIR identifiers with Rust paths, generated
  impl-block fragments, and names that may collide with Boole keywords.  This
  module centralizes the syntactic name policy used before BooleDDM lowering.
-/
import VerusLean.VLIR.Defs

namespace VerusLean.Boole.Names

open VerusLean

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

/-! ## Recognized Library Name Shapes -/

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

/-- Recognize `vstd::prelude::cloned` (ghost predicate asserting that the
    second argument is a clone of the first). For every `Clone` impl Verus
    admits, cloning is deterministic, so `cloned(x, y)` reduces to
    `x == y`. Matching on the name lets the translator rewrite without
    needing a prelude definition. -/
def isClonedName (name : Ident) : Bool :=
  let s := name.toString
  s.endsWith "::cloned" || s.endsWith ".cloned" || s == "cloned"

def isBoxNewName (name : Ident) : Bool :=
  identToBoole name == "Boxed_box_new"

def isArrayAsSliceName (name : Ident) : Bool :=
  identToBoole name == "Array_array_as_slice"

def isSliceIntoVecName (name : Ident) : Bool :=
  identToBoole name == "Slice_into_vec"

def isVecFromElemName (name : Ident) : Bool :=
  identToBoole name == "Vec_from_elem"

def isIndexSetName (name : Ident) : Bool :=
  identToBoole name == "Std_specs_Core_index_set"

/-- `vec2seq` branch: call targets that should be dropped during
    translation because the Vec surface collapses to `Sequence.*` ops.
    `Vec_from_elem` is the one kept stub (we synthesize a body for it);
    everything else named `Vec_*` or `Slice_into_vec` is a dead
    procedure with no Boole-side counterpart. -/
def isVec2SeqDroppedCalleeName (name : Ident) : Bool :=
  let n := identToBoole name
  (n.startsWith "Vec_" && n != "Vec_from_elem") || isSliceIntoVecName name

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
