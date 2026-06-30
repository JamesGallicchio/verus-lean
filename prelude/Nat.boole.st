// Nat prelude — always loaded.
//
// Hosts the `nat` type and the explicit `nat.toInt` / `nat.fromInt` API +
// round-trip axioms.  Lives in its own prelude (instead of the Seq prelude)
// because translator-emitted nat coercions can appear in any program, not
// just sequence-using ones.

type nat;

// --- Richer nat API ------------------------------------------------------
// Explicit toInt/fromInt API + round-trip axioms.  Lets cvc5 reason about
// nat-typed expressions via the embedding into int.  Boole-side arithmetic
// and comparisons are defined once (`nat.add`, `nat.lt`, …) so translator
// output doesn't need to splice `nat.toInt(...)` everywhere a nat appears
// in a binop.

function nat.toInt (n : nat) : int;

// Total, matching Verus's native `nat`: a `nat` result is non-negative by type,
// so coercion never carries a proof obligation. `nat.fromInt` is uninterpreted;
// the round-trip is pinned only for non-negative inputs (see `nat_fromInt_toInt`).
function nat.fromInt (x : int) : nat;

// Nat axioms
axiom [nat_nonneg]:        (forall n : nat :: 0 <= nat.toInt(n));
axiom [nat_fromInt_toInt]: (forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x);
axiom [nat_toInt_fromInt]: (forall n : nat :: nat.fromInt(nat.toInt(n)) == n);

// Nat operations
function nat.add (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) + nat.toInt(b)) }
// `nat.sub` is total, mirroring Verus's `nat - nat`: vir lowers it to int
// subtraction then a total `Clip` to nat (`nClip`), so `a < b` yields an
// unspecified nat, never a proof obligation. The value is pinned (== a - b)
// only when `b <= a`.
function nat.sub (a : nat, b : nat) : nat
{ nat.fromInt(nat.toInt(a) - nat.toInt(b)) }
function nat.mul (a : nat, b : nat) : nat { nat.fromInt(nat.toInt(a) * nat.toInt(b)) }
// Boole's `/` parses as `safediv_expr`, which Strata's encoder does not
// yet support; use the integer `div` keyword (`div_expr`) instead.
// `nat.div`/`nat.mod` are total, mirroring Verus's spec-level `/`/`%`, which are
// total: division by zero yields an unspecified value, never a proof obligation
// (vir's EucDiv/EucMod equal the SMT `div`/`mod`, whose bounds `0 <= . < y` are
// guarded by `0 < y`). For a zero divisor the result is some unspecified `nat`;
// the value is pinned only for a nonzero divisor, via the solver's native
// `div`/`mod`. (Exec `/`/`%` — where Rust panics on a zero divisor — would need
// a checked variant; this prelude models the spec operators.)
function nat.div (a : nat, b : nat) : nat
{ nat.fromInt(nat.toInt(a) div nat.toInt(b)) }
function nat.mod (a : nat, b : nat) : nat
{ nat.fromInt(nat.toInt(a) mod nat.toInt(b)) }

// Nat comparisons
function nat.lt (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt (a : nat, b : nat) : bool { nat.toInt(a) > nat.toInt(b) }
function nat.ge (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }
