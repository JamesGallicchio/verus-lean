// Seq prelude: declares Seq helper functions that wrap or extend
// Strata's built-in Sequence operations.  These are referenced by
// translated Verus specs but have no direct Strata built-in equivalent yet.
//
// Functions with Strata built-in equivalents have concrete bodies.
// Functions requiring higher-order operations (map, filter, sort, new)
// remain abstract.

type nat;

function int_to_nat(i: int): nat;

// --- Richer nat API ------------------------------------------------------
// Explicit toInt/fromInt API + round-trip axioms.  Lets cvc5 reason about
// nat-typed expressions via the embedding into int, much more reliably than
// the single uninterpreted `int_to_nat` coercion above (which has no inverse
// or nonneg axiom).  Boole-side arithmetic and comparisons are then defined
// once (`nat.add`, `nat.lt`, …) so translator output doesn't need to splice
// `nat.toInt(...)` everywhere a nat appears in a binop.

function nat.toInt      (n : nat) : int;
function nat.fromIntAux (x : int) : nat;

function nat.fromInt    (x : int) : nat
  requires 0 <= x;
{ nat.fromIntAux(x) }

// Nat axioms
axiom [nat_nonneg]:        (forall n : nat :: 0 <= nat.toInt(n));
axiom [nat_fromInt_toInt]: (forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x);
axiom [nat_toInt_fromInt]: (forall n : nat :: nat.fromInt(nat.toInt(n)) == n);

// Nat operations
function nat.add (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) + nat.toInt(b)) }
function nat.sub (a : nat, b : nat) : nat
  requires nat.toInt(b) <= nat.toInt(a);
{ nat.fromInt(nat.toInt(a) - nat.toInt(b)) }
function nat.mul (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) * nat.toInt(b)) }
// Boole's `/` parses as `safediv_expr`, which Strata's encoder does not
// yet support; use the integer `div` keyword (`div_expr`) instead.
function nat.div (a : nat, b : nat) : nat
  requires nat.toInt(b) != 0;
{ nat.fromInt(nat.toInt(a) div nat.toInt(b)) }
// `nat.mod` is intentionally commented out — see discussion about whether
// to expose it.  If reintroduced, route through `nat.fromIntAux` to skip the
// nonzero-divisor precondition (cvc5 can't always discharge `pow2(N) != 0`
// cheaply); the result for `mod 0` is then underspecified rather than
// ill-typed.
// function nat.mod (a : nat, b : nat) : nat { nat.fromIntAux(nat.toInt(a) mod nat.toInt(b)) }

// Nat comparisons
function nat.lt (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt (a : nat, b : nat) : bool { nat.toInt(a) >  nat.toInt(b) }
function nat.ge (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }

// --- End nat API ---------------------------------------------------------

type Set (T: Type);

// --- Concrete: defined using Strata built-ins ---

function Seq_len<T>(s: Sequence T): nat {
  int_to_nat(Sequence.length(s))
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
