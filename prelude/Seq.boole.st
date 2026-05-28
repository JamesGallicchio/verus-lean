// Seq prelude — loaded only when the program references sequence machinery
// (`Sequence.*` or any of the seq trigger names in
// `VerusLean/VLIR/Boole/Prelude.lean`).
//
// Declares Seq helper functions that wrap or extend Strata's built-in
// Sequence operations.  Functions with Strata built-in equivalents have
// concrete bodies; the higher-order ones (map/filter/sort/new) remain
// abstract.
//
// The `nat` type and its API live in `prelude/Nat.boole.st`, which is
// always loaded — `nat` shows up in many non-Seq programs too.

type Set (T: Type);

// --- Concrete: defined using Strata built-ins ---

// `nat.fromInt`'s `requires 0 <= x` is dischargeable from Strata's built-in
// `Sequence.length` nonneg axiom (`seqLengthFunc` in Core/Factory.lean).
function Seq_len<T>(s: Sequence T): nat {
  nat.fromInt(Sequence.length(s))
}

function Seq_lib_insert<T>(s: Sequence T, i: int, val: T): Sequence T {
  Sequence.append(Sequence.build(Sequence.take(s, i), val), Sequence.drop(s, i))
}

// --- Abstract: not yet expressible in Strata function bodies ---

// Requires iteration over `len` applying `f`.
function Seq_new<T>(len: nat, f: int -> T): Sequence T;

// Higher-order iteration.
function Seq_lib_map<T, U>(s: Sequence T, f: int -> T -> U): Sequence U;
function Seq_lib_map_values<T, U>(s: Sequence T, f: T -> U): Sequence U;
function Seq_lib_filter<T>(s: Sequence T, p: T -> bool): Sequence T;
function Seq_lib_sort_by<T>(s: Sequence T, less: T -> T -> bool): Sequence T;
// `Seq_lib_zip_with` is emitted as a SupportDecl in `SupportEmit.lean`
// rather than declared here — its return type `Sequence (Tuple A B)`
// references the `Tuple` datatype, which is itself emitted as a
// SupportDecl (via `requireSupport .tuple`). Declaring it here would
// fail to parse at prelude-load time, when `Tuple` is not yet in scope.

// Set operations — no Strata built-in.
function Seq_lib_to_set<T>(s: Sequence T): Set T;
function Set_finite<T>(s: Set T): bool;
