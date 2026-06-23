// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A1 "bool" (all green, stages 1-8).
// Demonstrates: boolean values and the logical connectives lower to Boole
// `bool` and discharge end-to-end.
use vstd::prelude::*;

verus! {

proof fn bool_connectives(a: bool, b: bool) {
    assert(a && b ==> a);
    assert(a ==> a || b);
    assert(!(a && b) <==> (!a || !b)); // De Morgan
    assert(a || !a);                   // excluded middle
    assert((a == b) <==> (a <==> b));
}

fn main() {}

} // verus!
