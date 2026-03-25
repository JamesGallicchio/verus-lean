program Core;

// Minimal typed prelude for emitted Verus Seq references.
// A richer future-facing design is kept separately in `Seq.future.core.st`.

type nat;

function nat_to_int(n: nat): int;
function int_to_nat(i: int): nat;

function bv64_to_int_u(x: bv64): int;
function bv64_to_nat_u(x: bv64): nat;
function int_to_bv64_u(x: int): bv64;

type Seq (T: Type);
type Set (T: Type);

function Seq_len<T>(s: Seq T): nat;
function Seq_empty<T>(): Seq T;
function Seq_index<T>(s: Seq T, i: int): T;
function Seq_first<T>(s: Seq T): T;
function Seq_last<T>(s: Seq T): T;
function Seq_update<T>(s: Seq T, i: int, v: T): Seq T;
function Seq_push<T>(s: Seq T, v: T): Seq T;
function Seq_take<T>(s: Seq T, n: int): Seq T;
function Seq_skip<T>(s: Seq T, n: int): Seq T;
function Seq_add<T>(s1: Seq T, s2: Seq T): Seq T;
function Seq_subrange<T>(s: Seq T, start_inclusive: int, end_exclusive: int): Seq T;
function Seq_new<T>(len: nat, f: int -> T): Seq T;
function Seq_lib_drop_last<T>(s: Seq T): Seq T;
function Seq_lib_contains<T>(s: Seq T, needle: T): bool;
function Seq_lib_remove<T>(s: Seq T, i: int): Seq T;
function Seq_lib_map<T, U>(s: Seq T, f: int -> T -> U): Seq U;
function Seq_lib_map_values<T, U>(s: Seq T, f: T -> U): Seq U;
function Seq_lib_filter<T>(s: Seq T, p: T -> bool): Seq T;
function Seq_lib_sort_by<T>(s: Seq T, less: T -> T -> bool): Seq T;
function Vec_view<T>(vec: Map bv64 T, vec_len: bv64): Seq T;
function Seq_lib_to_set<T>(s: Seq T): Set T;
function Set_finite<T>(s: Set T): bool;
