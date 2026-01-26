import Std.Data.HashMap

/-
  Verus `Seq`s are just Lean `List`s. All `Seq`s are finite.

  We define these new operations at the root "List" namespace.
  Alternatively, you can just map them to the underlying List operations
  in a translation table. But defining a List "shim" is more stable, I think.
-/

namespace List

variable {α : Type u} {β : Type v} {γ : Type w}

abbrev new (n : Nat) (f : Nat → α) : List α :=
  List.ofFn (n := n) (f := fun x => f x.val)

-- Note: Verus `Seq.index` is `List.getD` with default, so you will need `[Inhabited α]`
abbrev index [Inhabited α] (l : List α) (i : Nat) : α :=
  l.getD i default

abbrev push (l : List α) (a : α) : List α :=
  l ++ [a]

-- Maybe make `i` be an `Int`?
abbrev update (l : List α) (i : Nat) (a : α) : List α :=
  l.set i a



end List

#exit

-- namespace List, define some reimplementations, so we can refer to them in the translation table
/--
  Verus `Vstd` sequences. They are always finite.
-/
-- TODO: just use List for Seq, have a translation table
class VSeqLikeF (L : Type u → Type u) -- actually `Type 0 → Type 0` would be enough
  extends
    Functor L
  where
  toList : {α : Type u} → L α → List α
  ofList : {α : Type u} → List α → L α
  empty : {α : Type u} → L α :=
    ofList []
  -- for now keep the signature the same as in Verus, not `(f : Nat → α)`
  new {α : Type u} (len : Nat) (f : Int → α) : L α -- similar to List.ofFn but not the same
    := List.ofFn (n := len) (f := fun x => f x.val) |> ofList
  length : {α : Type u} → L α → Nat :=
    fun s => toList s |>.length
  get? : {α : Type u} → L α → Nat → Option α :=
    fun s i => (toList s)[i]?
  get [Inhabited α] : (s : L α) → (i : Nat) → (h : i < length s) → α :=
    fun s i _ => (toList s).getD i default
  get! [Inhabited α] : L α → Nat → α :=
    fun s i => (toList s).getD i default
  push : {α : Type u} → L α → α → L α :=
    fun s a => ofList ((toList s) ++ [a]) -- inefficient, Array.push is efficient
  update : {α : Type u} → L α → Nat → α → L α :=
    fun s i a => ofList ((toList s).set i a)
  extract : {α : Type u} → L α → Nat → Nat → L α :=
    fun s i j => ofList ((toList s).extract i j)
  take : {α : Type u} → L α → Nat → L α := -- return the whole seq if n > length
    fun s n => ofList ((toList s).take n)
  drop : {α : Type u} → L α → Nat → L α := -- return the empty seq if n > length
    fun s n => ofList ((toList s).drop n)
  add : {α : Type u} → L α → L α → L α :=
    fun s₁ s₂ => ofList ((toList s₁) ++ (toList s₂))
  last [Inhabited α] : L α → α := -- if empty, return a default value, or requires `length s > 0`?
    fun s => (toList s).getLastD default
  first [Inhabited α] : L α → α := -- same as above
    fun s => (toList s).headD default

  mapEntries : {α β : Type u} → L α → (Int → α → β) → L β :=
    fun s f => ofList ((toList s).zipIdx.map fun (x,i) => f i x)
  isPrefixOf [BEq α] : L α → L α → Bool :=
    fun s₁ s₂ => (toList s₁).isPrefixOf (toList s₂)
  isSuffixOf [BEq α] : L α → L α → Bool :=
    fun s₁ s₂ => (toList s₁).isSuffixOf (toList s₂)
  sortBy {α : Type u} (pred : α → α → Bool) : L α → L α
   := fun l => List.mergeSort (toList l) pred |> ofList
  filter : {α : Type u} → (L α) → (α → Bool) → L α :=
    fun s p => ofList ((toList s).filter p)
  maxVia [Inhabited α] : (L α) → (α → α → Bool) → α
  minVia [Inhabited α] : (L α) → (α → α → Bool) → α
  mem : {α : Type u} → (L α) → α → Prop :=
    fun s a => a ∈ (toList s)
  indexOf [BEq α] : (L α) → α → Int :=
    fun s a => (toList s).idxOf a
  indexOfFirst [BEq α] : (L α) → α → Option Int :=
    fun s a => (toList s).idxOf? a
  -- firstIndexHelper : {α : Type u} → (L α) → α → Int
  indexOfLast [BEq α] : (L α) → α → Option Int
  -- lastIndexHelper : {α : Type u} → (L α) → α → Int
  dropLast : {α : Type u} → L α → L α :=
    fun s => ofList ((toList s).dropLast)
  dropFirst : {α : Type u} → L α → L α :=
    fun s => ofList ((toList s).tail)
  noDuplicates : {α : Type u} → L α → Prop :=
    fun s => (toList s).Nodup
  disjoint : {α : Type u} → L α → L α → Prop :=
    fun s₁ s₂ => (toList s₁).Disjoint (toList s₂)
  insert : {α : Type u} → L α → Nat → α → L α :=
    fun s i a => ofList ((toList s).insertIdx i a)
  remove : {α : Type u} → L α → Nat → L α :=
    fun s i => ofList ((toList s).eraseIdx i)
  removeValue [BEq α] : L α → α → L α :=
    fun s a => ofList ((toList s).erase a)
  reverse : {α : Type u} → L α → L α :=
    fun s => ofList ((toList s).reverse)
  zipWith : {α β : Type u} → L α → L β → L (α × β) := -- if different lengths, returns an empty sequence
    fun s₁ s₂ => if length s₁ ≠ length s₂ then empty else ofList ((toList s₁).zip (toList s₂))
  foldLeft : {α β : Type u} → L α → β → (β → α → β) → β :=
    fun s init f => (toList s).foldl f init -- not the same implementation as in Verus
  foldLeftAlt : {α β : Type u} → L α → β → (β → α → β) → β :=
    fun s init f => (toList s).foldl f init
  foldRight : {α β : Type u} → L α → (α → β → β) → β → β :=
    fun s f init => (toList s).foldr f init -- not the same implementation as in Verus
  foldRightAlt : {α β : Type u} → L α → (α → β → β) → β → β :=
    fun s f init => (toList s).foldr f init
  updateSubrangeWith : {α : Type u} → L α → Nat → L α → L α :=
    fun s i t => ofList ((toList s).take i ++ (toList t) ++ (toList s).drop (i + length t))

  unzip : {α β : Type u} → L (α × β) → L α × L β :=
    fun s => (ofList ((toList s).unzip.fst), ofList ((toList s).unzip.snd))
  flatten : {α : Type u} → L (L α) → L α :=
    fun s => ofList ((toList s).map toList |>.flatten)
  flatten_alt : {α : Type u} → L (L α) → L α :=
    fun s => ofList ((toList s).map toList |>.flatten) -- not the same implementation as in Verus
/-
  max [Inhabited α] [Max α] : L α → α :=
    fun s => (toList s).max?.getD default
  min [Inhabited α] [Min α] : L α → α :=
    fun s => (toList s).min?.get!
  sort [LE α] : L α → L α :=
    fun s => ofList ((toList s).mergeSort)
  merge_sorted_with : {α : Type u} → L α → L α → (α → α → Bool) → L α -/
  -- seq_to_set_rec

namespace VSeqLikeF

variable {L : Type u → Type u} [VSeqLikeF L]

instance instEmptyCollection : EmptyCollection (L α) := ⟨empty⟩
instance instInhabited : Inhabited (L α) := ⟨∅⟩
instance instSingleton : Singleton α (L α) := ⟨fun a => push empty a⟩
instance instMembership : Membership α (L α) := ⟨mem⟩
instance instInsert : Insert α (L α) := ⟨fun a s => push s a⟩
instance instHAdd : HAdd (L α) (L α) (L α) := ⟨add⟩
instance instCoeList : Coe (List α) (L α) := ⟨ofList⟩
instance instGetElem [Inhabited α] : GetElem (L α) Nat α (fun s i => i < length s) := ⟨get⟩
instance instGetElem? [Inhabited α] : GetElem? (L α) Nat α (fun s i => i < length s) where
  getElem? := get?
  getElem! := get!

end VSeqLikeF

-- 1. define toList and fromList, show round trip => inherit all List functions and lemmas
-- TODO: check James' LeanColls!
-- e.g. append s t = ofList (List.append (toList s) (toList t)), or say, toList (append s t) = List.append (toList s) (toList t)

-- 2. Current approach, and show that show List is an instance of Seq
-- write theorems for the type class (a shim around the underlying List theorem?)
-- In both cases, L α is isomorphic to List α?

open VSeqLikeF in
class LawfulVSeqLikeF (L : Type u → Type u) [VSeqLikeF L]
  extends
    LawfulFunctor L
  where
  protected ext (s₁ s₂ : L α) : (length s₁ = length s₂ ∧ ∀ i, i < length s₁→ get? s₁ i = get? s₂ i) → s₁ = s₂
  roundtrip : ∀ {α : Type u} (s : L α), ofList (toList s) = s
  ax_empty : [] = toList (empty : L α)

  -- TODO Do we want all these below:
  length_empty : length (empty : L α) = 0
  length_new {α : Type u} (len : Nat) (f : Int → α) : length (new len f : L α) = len
  length_push {α : Type u} (s : L α) (a : α) : length (push s a) = length s + 1
  length_update {α : Type u} (s : L α) (i : Nat) (a : α) (h : i < length s) :
    length (update s i a) = length s
  length_extract {α : Type u} (s : L α) (i j : Nat) (h₁ : i ≤ j) (h₂ : j ≤ length s) :
    length (extract s i j) = j - i
  length_take {α : Type u} (s : L α) (n : Nat) : length (take s n) = if n < length s then n else length s
  length_drop {α : Type u} (s : L α) (n : Nat) : length (drop s n) = if n < length s then length s - n else 0
  length_add {α : Type u} (s₁ s₂ : L α) : length (s₁ + s₂) = length s₁ + length s₂
  length_last {α : Type u} (s : L α) (h : length s > 0) : length (dropLast s) = length s - 1
  length_first {α : Type u} (s : L α) (h : length s > 0) : length (dropFirst s) = length s - 1
  length_map {α β} (f : α → β) (s : L α) : length (f <$> s) = length s

  get?_empty {α} (i : Nat) : get? (empty : L α) i = none
  get?_push {α} (s : L α) (a : α) (i : Nat) :
    get? (push s a) i = if i = length s then some a else get? s i
  get?_update {α} (s : L α) (i j : Nat) (a : α) :
    get? (update s i a) j = if i = j then some a else get? s j
  get?_extract {α} (s : L α) (i j k: Nat) : -- I think no need to check pos in range?
    get? (extract s i j) k = get? s (i + k)
  get?_take {α} (s : L α) (n i : Nat):
    get? (take s n) i = if i < n then get? s i else none
  get?_drop {α} (s : L α) (n i : Nat) :
    get? (drop s n) i = get? s (n + i)
  get?_add {α} (s₁ s₂ : L α) (i : Nat) :
    get? (s₁ + s₂) i = if i < length s₁ then get? s₁ i else get? s₂ (i - length s₁)
  get?_last {α} [Inhabited α] (s : L α) (h : length s > 0) : get? s (length s - 1) = some (last s)
  get?_first {α} [Inhabited α] (s : L α) (h : length s > 0) : get? s 0 = some (first s)
  get?_map {α β} [Inhabited α] (f : α → β) (s : L α) (i : Nat) :
    get? (f <$> s) i = if i < length s then some (f (get! s i)) else none

  extract_eq {α} (s : L α) (i j : Nat) :
    extract s i j = take (drop s i) (j - i)

  mem_iff_exists_get {α} (s : L α) (a : α) :
    a ∈ s ↔ ∃ i, i < length s ∧ get? s i = some a

  filter_empty {α} (p : α → Bool) : filter (empty : L α) p = empty
  filter_push {α} (s : L α) (a : α) (p : α → Bool) :
    filter (push s a) p = if p a then push (filter s p) a else filter s p
  -- filter_pred {α} (s : L α) (p : α → Bool) (h : i < length (filter s p)) :
    -- p (get (filter s p) i h)

  eq_push_last {α} [Inhabited α] (s : L α) (h : length s > 0) :
    (push (dropLast s) (last s)) = s
  eq_push_first_to_drop_first {α} [Inhabited α] (s : L α) (h : length s > 0) :
    (push (dropFirst s) (first s)) = s

  dropLast_eq {α} (s : L α) (h : length s > 0) :
    dropLast s = extract s 0 (length s - 1)
  dropFirst_eq {α} (s : L α) (h : length s > 0) :
    dropFirst s = extract s 1 (length s)

-- TODO: write definitions outside the type class, e.g. unzip via map
def unzip {α β : Type u} [VSeqLikeF L] (s : L (α × β)) : L α × L β :=
  (Functor.map Prod.fst s, Functor.map Prod.snd s)

open LawfulVSeqLikeF in
-- attribute [simp] not_mem_empty mem_singleton_iff mem_ofList_iff
-- attribute [ext] LawfulVSeqLikeF.ext

class FoldCommutative (op : α → β → α) : Prop where
  comm : (a : α) → (b₁ b₂ : β) → op (op a b₁) b₂ = op (op a b₂) b₁

class FoldCommutativeR (op : α → β → β) : Prop where
  comm : (a₁ a₂ : α) → (b : β) → op a₁ (op a₂ b) = op a₂ (op a₁ b)

end Vstd
