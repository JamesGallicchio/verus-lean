// Seq prelude: declares Seq helper functions that wrap or extend
// Strata's built-in Sequence operations.  These are referenced by
// translated Verus specs but have no direct Strata built-in equivalent yet.
//
// Functions with Strata built-in equivalents have concrete bodies.
// Functions requiring higher-order operations (map, filter, sort, new)
// remain abstract. The translator-managed numeric support layer supplies
// `type nat;`, `nat_to_int`, and `int_to_nat`; this prelude just depends on
// those declarations.

type Set (T: Type);

// --- Concrete: defined using Strata Core built-ins ---

function Seq_len<T>(s: Sequence T): nat {
  int_to_nat(Sequence.length(s))
}

function Seq_lib_insert<T>(s: Sequence T, i: int, val: T): Sequence T {
  Sequence.append(Sequence.build(Sequence.take(s, i), val), Sequence.drop(s, i))
}

// --- Abstract: not yet expressible in Strata Core ---

// Requires iteration over `len` applying `f` — Core functions have no loops.
function Seq_new<T>(len: nat, f: int -> T): Sequence T;

// Higher-order iteration — not expressible without loops/recursion.
function Seq_lib_map<T, U>(s: Sequence T, f: int -> T -> U): Sequence U;
function Seq_lib_map_values<T, U>(s: Sequence T, f: T -> U): Sequence U;
function Seq_lib_filter<T>(s: Sequence T, p: T -> bool): Sequence T;
function Seq_lib_sort_by<T>(s: Sequence T, less: T -> T -> bool): Sequence T;

// Set operations — no Strata built-in.
function Seq_lib_to_set<T>(s: Sequence T): Set T;
function Set_finite<T>(s: Set T): bool;
