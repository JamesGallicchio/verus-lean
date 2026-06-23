// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B6 "`opaque` + `reveal` (non-generic)" (all green).
// Demonstrates: an `#[verifier::opaque]` spec function is an uninterpreted
// symbol until `reveal` makes its body visible (lowered to `assume forall`).
use vstd::prelude::*;

verus! {

#[verifier::opaque]
spec fn secret(x: int) -> int {
    x * 3
}

// Without `reveal`: only reflexivity is available (body hidden).
proof fn opaque_hidden() {
    assert(secret(2) == secret(2));
}

// With `reveal`: the body becomes usable.
proof fn revealed() {
    reveal(secret);
    assert(secret(2) == 6);
}

fn main() {}

} // verus!
