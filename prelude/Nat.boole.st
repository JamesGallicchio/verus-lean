// Nat prelude — always loaded.
//
// Hosts the `nat` type and the explicit `nat.toInt` / `nat.fromInt` API +
// round-trip axioms.  Lives in its own prelude (instead of the Seq prelude)
// because translator-emitted nat coercions can appear in any program with
// `nat`-typed expressions, not just sequence-using ones.

type nat;

// --- Richer nat API ------------------------------------------------------
// Explicit toInt/fromInt API + round-trip axioms.  Lets cvc5 reason about
// nat-typed expressions via the embedding into int.  Boole-side arithmetic
// and comparisons are defined once (`nat.add`, `nat.lt`, …) so translator
// output doesn't need to splice `nat.toInt(...)` everywhere a nat appears
// in a binop.

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
// `nat.mod` mirrors `nat.div`: a nonzero-divisor precondition, with the Euclidean
// remainder non-negative so `nat.fromInt` is well-defined.  The precondition
// guards the value axiom, so reasoning about a bare `nat.mod` value (e.g. parity
// under an equality) is limited — callers needing the value cannot treat it
// transparently — but the prelude stays consistent with `nat.div`.
function nat.mod (a : nat, b : nat) : nat
  requires nat.toInt(b) != 0;
{ nat.fromInt(nat.toInt(a) mod nat.toInt(b)) }

// Nat comparisons
function nat.lt (a : nat, b : nat) : bool { nat.toInt(a) <  nat.toInt(b) }
function nat.le (a : nat, b : nat) : bool { nat.toInt(a) <= nat.toInt(b) }
function nat.gt (a : nat, b : nat) : bool { nat.toInt(a) > nat.toInt(b) }
function nat.ge (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }
