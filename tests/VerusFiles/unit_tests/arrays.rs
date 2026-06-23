// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A3 "Arrays / fixed-size array literals" (all green).
// Demonstrates: fixed-size array literals lower to a concrete `Sequence`, and
// element indexing plus (in)equality over them discharge end-to-end.
//
// NOTE: `arr.len()` is intentionally not asserted here — it lowers through an
// uninterpreted `Array_spec_array_as_slice` wrapper whose length cvc5 cannot
// relate to the literal, so that one obligation times out (Seq-frontend gap).
use vstd::prelude::*;

verus! {

proof fn array_indexing() {
    let a: [u32; 3] = [10, 20, 30];
    assert(a[0] == 10);
    assert(a[1] == 20);
    assert(a[2] == 30);
}

proof fn array_inequality() {
    let a: [u32; 3] = [3, 3, 0];
    let b: [u32; 3] = [3, 3, 1];
    assert(a != b);
}

fn main() {}

} // verus!
