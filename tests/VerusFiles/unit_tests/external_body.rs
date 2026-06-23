// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B1 "`external_body` / trusted specs" (all green).
// Demonstrates: an `#[verifier::external_body]` function is trusted — its body
// is not verified (emitted with the `assume false;` convention) but its
// `ensures` is available to callers.
use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn trusted_id(x: u32) -> (r: u32)
    ensures r == x,
{
    x // body is trusted, not verified
}

fn use_trusted() {
    let v = trusted_id(42);
    assert(v == 42); // provable only via the trusted `ensures`
}

fn main() {}

} // verus!
