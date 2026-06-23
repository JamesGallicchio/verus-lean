// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B4 "`choose` operator" ([TRANS-choose] #1365, all green).
// Demonstrates: `choose|x| P(x)` selects a witness; once existence is
// established, the chosen value satisfies the predicate. The predicate is a
// spec function so Verus can infer the trigger (`big(i)`).
use vstd::prelude::*;

verus! {

spec fn big(i: int) -> bool { i > 10 }

proof fn choose_witness() {
    assert(big(11));                  // 11 satisfies the predicate
    assert(exists|i: int| big(i));    // so a witness exists
    let x = choose|i: int| big(i);    // choose one
    assert(big(x));                   // the chosen value satisfies the predicate
    assert(x > 10);                   // ... which unfolds to x > 10
}

fn main() {}

} // verus!
