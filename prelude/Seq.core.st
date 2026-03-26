program Core;

// Minimal typed prelude for emitted Verus Seq references.
// A richer future-facing design is kept separately in `Seq.future.core.st`.

type nat;

function nat_to_int(n: nat): int;
function int_to_nat(i: int): nat;

function bv64_to_int_u(x: bv64): int;
function bv64_to_nat_u(x: bv64): nat;
function int_to_bv64_u(x: int): bv64;

type Set (T: Type);

function Seq_len<T>(s: Sequence T): nat;
function Seq_new<T>(len: nat, f: int -> T): Sequence T;
function Seq_lib_map<T, U>(s: Sequence T, f: int -> T -> U): Sequence U;
function Seq_lib_map_values<T, U>(s: Sequence T, f: T -> U): Sequence U;
function Seq_lib_filter<T>(s: Sequence T, p: T -> bool): Sequence T;
function Seq_lib_sort_by<T>(s: Sequence T, less: T -> T -> bool): Sequence T;
function Vec_view<T>(vec: Map bv64 T, vec_len: bv64): Sequence T;
function Seq_lib_to_set<T>(s: Sequence T): Set T;
function Set_finite<T>(s: Set T): bool;
