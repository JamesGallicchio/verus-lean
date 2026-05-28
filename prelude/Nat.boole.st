// Nat prelude — always loaded.
//
// Hosts the `nat` type, the `int_to_nat` legacy coercion, and the explicit
// `nat.toInt` / `nat.fromInt` API + round-trip axioms.  Lives in its own
// prelude (instead of the Seq prelude) because translator-emitted nat
// coercions can appear in any program with `nat`-typed expressions, not
// just sequence-using ones.

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
function nat.gt (a : nat, b : nat) : bool { nat.toInt(a) > nat.toInt(b) }
function nat.ge (a : nat, b : nat) : bool { nat.toInt(a) >= nat.toInt(b) }
