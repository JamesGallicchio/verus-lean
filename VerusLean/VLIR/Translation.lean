import VerusLean.VLIR.Defs
import VerusLean.Vstd.Seq.Defs
import VerusLean.Vstd.Set.Defs
import VerusLean.Vstd.Map.Defs
import Lean.Elab

namespace VerusLean

open Lean
/-
def combine2Maps (map1 map2 : Std.HashMap Ident Ident) : Std.HashMap Ident Ident :=
  map2.fold (fun acc k v => acc.insert k v) map1
def combineMaps (maps : List (Std.HashMap Ident Ident)) : Std.HashMap Ident Ident :=
  maps.foldl (fun acc map => combine2Maps acc map) Std.HashMap.emptyWithCapacity
private def TranslationNames : Std.HashMap Ident Ident :=
  combineMaps [Vstd.SetVstdTranslationNames, Vstd.SetLibVstdTranslationNames,
              Vstd.MapVstdTranslationNames, Vstd.MapLibVstdTranslationNames,
              Vstd.SeqVstdTranslationNames, Vstd.SeqLibVstdTranslationNames]
 -/

def translateSyntaxOriginal (fn : Lean.Ident) (params : List Term) : CoreM Term := do
  let init ← `($fn:ident)
  params.foldlM (init := init) (fun acc t => do
    `($acc:term ($t:term)))

def translateSyntaxView (_ : Lean.Ident) (params : List Term) : CoreM Term := do
  match params with
    | [] => panic! "Vstd.View.view function called with no arguments"
    | t :: ts =>
      ts.foldlM (init := t) (fun acc t => `($acc:term $t:term))

def translateSyntaxContains (fn : Lean.Ident) (params : List Term) : CoreM Term := do
  if params.length != 2 then
    panic! s!"{fn} expects 2 arguments, got {params.length}"
  else
    let s := params[0]!
    let e := params[1]!
    `($e:term ∈ $s:term)

/- There are some problems with translating to notations such as ∈, []!, etc.
   For example, although we did define instances `instHAdd` and `instHAddSingleton`,
   Lean will fail to infer the types in `∅ + 5` because they are not outParams,
   unless we write it explicitly as: `(∅ : Set Nat) + (5 : Nat)`.
   For `GetElem`, since `idx` is not an outParam, if we have `m : Vstd.Map Int Int`,
   Lean will not know that the `20` in `m[20]! = 200` is an Int, we must write
   `m[(20:Int)]! = 200` instead. Translating to functions is fine without specifying the types.
-/
def translateSyntaxIndex (fn : Lean.Ident) (params : List Term) : CoreM Term := do
  if params.length != 2 then
    panic! s!"{fn} expects 2 arguments, got {params.length}"
  else
    let m := params[0]!
    let k := params[1]!
    `($m:term[$k:term]!)

def VstdSyntaxTable :
    Std.HashMap Lean.Name (Lean.Name × (Lean.Ident → List Term → CoreM Term)) :=
  (Std.HashMap.ofList <|
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Set.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("empty", "Set.empty"), -- or do we translate them to VSetF, by default assuming finite sets?
  ("new", "VSetInfF.new"), -- VSetInfF.new
  ("full", "VSetInfF.full"), -- might be an infinite set
  ("contains", "Set.mem"),
  ("spec_has", "Set.mem"),
  ("subset_of", "Set.subset"),
  ("spec_le", "Set.subset"),
  ("insert", "Set.insert"),
  ("remove", "Set.remove"),
  ("union", "Set.union"),
  ("spec_add", "Set.union"),
  ("intersect", "Set.inter"),
  ("spec_mul", "Set.inter"),
  ("difference", "Set.sdiff"),
  ("spec_sub", "Set.sdiff"),
  ("complement", "VSetInfF.compl"), -- might become an infinite set when taking complement
  ("filter", "Set.filter"),
  ("finite", "VSetInfF.isFinite"), -- should be a property of the generic VSetLikeF instead
  ("len", "Set.card"), -- assuming finiteness
  -- CZ: the signature now matches, if we don't require a hypothesis that the set is inhabited
  ("choose", "Set.choose"), -- The signatures for choose don't match
  ("mk_map", "VMapLikeF.fromSet"),
  ("disjoint", "Set.disjoint"),
  ("Fold.fold", "Set.fold"),
  ])
  ++
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Set_lib.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("is_full", "VSetInfF.isFull"),
  ("is_empty", "VSetLikeF.isEmpty"),
  ("map", "Set.map"),
  ("to_seq", ""),
  ("to_sorted_seq", ""),
  ("is_singleton", "VSetLikeF.isSingleton"),
  ("find_unique_minimal", "VSetLikeF.findUniqueMinimal"),
  ("find_unique_maximal", "VSetLikeF.findUniqueMaximal"),
  ("to_multiset", ""), -- ignored for now
  ("all", "VSetLikeF.all"),
  ("any", "VSetLikeF.any"),
  ("filter_map", "Set.filterMap"),
  ("flatten", ""), -- ignored for now, as its type is different
  ("set_int_range", "VSetLikeF.setIntRange"), -- if a set contains ints in [a,b), its size is bounded by b-a
  ])
  ++
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Map.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("empty", "VMapLikeF.empty"),
  -- There is a discussion about set.mk_map: https://github.com/verus-lang/verus/discussions/1666
  ("total", "VMapLikeF.total"), -- do we want an infinite map type class?
  ("new", "VMapLikeF.new"),
  ("dom", "VMapLikeF.domain"),
   /- Verus: For keys not in the domain, the result is meaningless and arbitrary.
      But Lean will panic if key not in domain.
      `get` and `get?` don't have the same signature as `index`. -/
  ("index", "VMapLikeF.get!"),
  ("spec_index", "VMapLikeF.get!"), -- same as index
  ("insert", "VMapLikeF.insert"),
  ("remove", "VMapLikeF.remove"),
  ("len", "VMapLikeF.size"), -- or LawfulVMapLikeF.size?
  ])
  ++
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Map_lib.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("is_full", "VMapLikeF.keys |> VSetInfF.full"), -- need something beyond a translation table to operate on the domain set
  ("is_empty", "VMapLikeF.keys |> VSetLikeF.empty"), -- same
  ("contains_key", "VMapLikeF.memKeys"),
  ("contains_value", "VMapLikeF.memValues"),
  ("index_opt", "VMapLikeF.get?"),
  ("values", "VMapLikeF.values"),
  ("contains_pair", "VMapLikeF.instMembership"), -- not sure
  ("submap_of", "VMapLikeF.submapOf"),
  ("spec_le", "VMapLikeF.submapOf"), -- same as submap_of
  ("union_prefer_right", "VMapLikeF.union_prefer_right"),
  ("remove_keys", "VMapLikeF.removeKeys"),
  ("restrict", "VMapLikeF.restrict"),
  ("is_equal_on_key", "VMapLikeF.isEqualOnKey"),
  ("agrees", "VMapLikeF.agrees"),
  ("map_entires", "VMapLikeF.mapEntries"),
  ("map_values", "VMapLikeF.mapValues"),
  ("is_injective", "VMapLikeF.isInjective"),
  ("invert", "")
  ])
  ++
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Seq.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("empty", "VSeqLikeF.empty"),
  ("new", "VSeqLikeF.new"),
  ("len", "VSeqLikeF.length"),
  ("index", "VSeqLikeF.get!"), -- direct indexing s[i] is supported via getElem
  ("spec_index", "VSeqLikeF.get!"), -- same as index
  ("push", "VSeqLikeF.push"),
  ("update", "VSeqLikeF.update"),
  ("subrange", "VSeqLikeF.extract"),
  ("take", "VSeqLikeF.take"),
  ("skip", "VSeqLikeF.drop"),
  ("add", "VSeqLikeF.add"),
  ("spec_add", "VSeqLikeF.add"), -- same as add
  ("last", "VSeqLikeF.last"),
  ("first", "VSeqLikeF.first"),
  ])
  ++
  (List.map (f := fun (x, y) => (String.toName s!"Vstd.Seq_lib.{x}", (String.toName y, translateSyntaxOriginal))) <|
  [("map", "VSeqLikeF.mapEntries"), -- Verus TODO: rename to `map_entries`?
  ("map_values", "Functor.map"), -- Verus TODO: rename to `map`?
  ("is_prefix_of", "VSeqLikeF.isPrefixOf"),
  ("is_suffix_of", "VSeqLikeF.isSuffixOf"),
  ("sort_by", "VSeqLikeF.sortBy"),
  ("filter", "VSeqLikeF.filter"),
  ("max_via", "VSeqLikeF.maxVia"),
  ("min_via", "VSeqLikeF.minVia"),
  ("contains", "VSeqLikeF.mem"),
  ("index_of", "VSeqLikeF.indexOf"),
  ("index_of_first", "VSeqLikeF.indexOfFirst"),
  ("first_index_helper", ""),
  ("index_of_last", "VSeqLikeF.indexOfLast"),
  ("last_index_helper", ""),
  ("drop_last", "VSeqLikeF.dropLast"),
  ("drop_first", "VSeqLikeF.dropFirst"),
  ("no_duplicates", "VSeqLikeF.noDuplicates"),
  ("disjoint", "VSeqLikeF.disjoint"),
  ("to_set", "VSetLikeF.fromSeq"),
  ("to_multiset", ""), -- ignored for now
  ("insert", "VSetLikeF.insert"),
  ("remove", "VSetLikeF.remove"),
  ("remove_value", "VSetLikeF.removeValue"),
  ("reverse", "VSetLikeF.reverse"),
  ("zip_with", "VSetLikeF.zipWith"),
  ("fold_left", "VSetLikeF.foldLeft"),
  ("fold_left_alt", "VSetLikeF.foldLeftAlt"),
  ("fold_right", "VSetLikeF.foldRight"),
  ("fold_right_alt", "VSetLikeF.foldRightAlt"),
  ("update_subrange_with", "VSetLikeF.updateSubrangeWith"),

  ("unzip", "VSeqLikeF.unzip"),
  ("flatten", "VSeqLikeF.flatten"),
  ("flatten_alt", "VSeqLikeF.flatten_alt"),

  ("max", "VSeqLikeF.max"),
  ("min", "VSeqLikeF.min"),
  ("sort", "VSeqLikeF.sort"),
  ("merge_sorted_with", "VSeqLikeF.merge_sorted_with"),

  ("seq_to_set_rec", ""),
  ]))
  |>.insert (String.toName "Vstd.View.view")
    (String.toName "Vstd.View.view", translateSyntaxView)
  |>.insert (String.toName "Vstd.Set.contains")
    (String.toName "∈", translateSyntaxContains)
  |>.insert (String.toName "Vstd.Map.index")
    (String.toName "", translateSyntaxIndex)
  |>.insert (String.toName "Vstd.Map.spec_index")
    (String.toName "", translateSyntaxIndex)
  |>.insert (String.toName "Vstd.Seq.index")
    (String.toName "", translateSyntaxIndex)
  |>.insert (String.toName "Vstd.Seq.spec_index")
    (String.toName "", translateSyntaxIndex)
