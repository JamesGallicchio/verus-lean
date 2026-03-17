program Core;

// Standalone Core prelude sketch for Verus Seq helpers.
//
// This file is not wired into the translator yet. It records a future-facing
// model for first-order sequence operations that matches the intent of
// `vstd/seq.rs` and the first-order parts of `vstd/seq_lib.rs`, instead of the
// current ad hoc uninterpreted-function stubs emitted in generated `.core.st`
// files.
//
// Design choices:
// - `nat` is emitted as a nominal type, matching the current translation
//   direction we want for Verus nat.
// - `Seq` is a real recursive datatype, so first-order sequence combinators can
//   be defined by body.
// - Out-of-range indexing uses `Arbitrary` rather than inventing partial
//   function syntax.
//
// Still blocked on Strata/Core support:
// - higher-order function arguments (`arrow`) needed for `Seq_new`, `map`,
//   `filter`, `sort_by`, etc.
// - native `Set` / `Multiset`
// - nat arithmetic / literals / recursion support robust enough to accept the
//   intended bodies below without approximation

type nat;

datatype Seq (T: Type) {
  Seq_nil();
  Seq_cons(head: T, tail: Seq(T));
}

function Arbitrary<T>(): T;

function Seq_empty<T>(): Seq(T) {
  Seq_nil()
}

rec function Seq_len<T>(s: Seq(T)): nat {
  if Seq.isSeq_nil(s) then
    0
  else
    1 + Seq_len(Seq.tail(s))
}

rec function Seq_index<T>(s: Seq(T), i: int): T {
  if Seq.isSeq_nil(s) then
    Arbitrary()
  else if i == 0 then
    Seq.head(s)
  else if i > 0 then
    Seq_index(Seq.tail(s), i - 1)
  else
    Arbitrary()
}

rec function Seq_add<T>(s1: Seq(T), s2: Seq(T)): Seq(T) {
  if Seq.isSeq_nil(s1) then
    s2
  else
    Seq_cons(Seq.head(s1), Seq_add(Seq.tail(s1), s2))
}

function Seq_push<T>(s: Seq(T), a: T): Seq(T) {
  Seq_add(s, Seq_cons(a, Seq_nil()))
}

rec function Seq_update<T>(s: Seq(T), i: int, a: T): Seq(T) {
  if Seq.isSeq_nil(s) then
    Seq_nil()
  else if i == 0 then
    Seq_cons(a, Seq.tail(s))
  else if i > 0 then
    Seq_cons(Seq.head(s), Seq_update(Seq.tail(s), i - 1, a))
  else
    s
}

rec function Seq_take<T>(s: Seq(T), n: int): Seq(T) {
  if n <= 0 then
    Seq_nil()
  else if Seq.isSeq_nil(s) then
    Seq_nil()
  else
    Seq_cons(Seq.head(s), Seq_take(Seq.tail(s), n - 1))
}

rec function Seq_skip<T>(s: Seq(T), n: int): Seq(T) {
  if n <= 0 then
    s
  else if Seq.isSeq_nil(s) then
    Seq_nil()
  else
    Seq_skip(Seq.tail(s), n - 1)
}

function Seq_subrange<T>(s: Seq(T), start_inclusive: int, end_exclusive: int): Seq(T) {
  if 0 <= start_inclusive && start_inclusive <= end_exclusive then
    Seq_take(Seq_skip(s, start_inclusive), end_exclusive - start_inclusive)
  else
    Seq_nil()
}

function Seq_first<T>(s: Seq(T)): T {
  Seq_index(s, 0)
}

rec function Seq_last<T>(s: Seq(T)): T {
  if Seq.isSeq_nil(s) then
    Arbitrary()
  else if Seq.isSeq_nil(Seq.tail(s)) then
    Seq.head(s)
  else
    Seq_last(Seq.tail(s))
}

rec function Seq_lib_drop_last<T>(s: Seq(T)): Seq(T) {
  if Seq.isSeq_nil(s) then
    Seq_nil()
  else if Seq.isSeq_nil(Seq.tail(s)) then
    Seq_nil()
  else
    Seq_cons(Seq.head(s), Seq_lib_drop_last(Seq.tail(s)))
}

function Seq_lib_contains<T>(s: Seq(T), needle: T): bool {
  exists i: int :: 0 <= i && i < Seq_len(s) && Seq_index(s, i) == needle
}

function Seq_lib_remove<T>(s: Seq(T), i: int): Seq(T) {
  Seq_add(Seq_take(s, i), Seq_skip(s, i + 1))
}

// Future work once Strata/Core supports higher-order arguments and collection
// categories well enough for faithful Verus modeling:
//
// function Seq_new<T>(len: nat, f: int -> T): Seq(T);
// function Seq_lib_map<T, U>(s: Seq(T), f: T -> U): Seq(U);
// function Seq_lib_map_values<T, U>(s: Seq(T), f: T -> U): Seq(U);
// function Seq_lib_filter<T>(s: Seq(T), p: T -> bool): Seq(T);
// function Seq_lib_sort_by<T>(s: Seq(T), less: T -> T -> bool): Seq(T);
// function Seq_lib_to_set<T>(s: Seq(T)): Set(T);
// function Seq_lib_to_multiset<T>(s: Seq(T)): Multiset(T);
//
// Vec adapters should be thin wrappers over this sequence layer, but the
// current translator still lowers exec Vecs with a different carrier and
// signature shape, so those wrappers are intentionally omitted here.
