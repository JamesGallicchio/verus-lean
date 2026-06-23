// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B4 "Quantifiers (`forall` / `exists`)" (all green).
// Demonstrates: universal and existential quantifiers lower to Boole
// `forall`/`exists` and discharge end-to-end. Bodies are phrased over a spec
// function so Verus can infer a trigger (`f(x)`) automatically.
use vstd::prelude::*;

verus! {

spec fn f(x: int) -> int { x + 1 }

proof fn quantifiers() {
    assert(forall|x: int| f(x) == x + 1); // universal; trigger f(x)
    assert(f(5) == 6);                    // ground witness for the existential
    assert(exists|x: int| f(x) == 6);     // existential; trigger f(x)
}

fn main() {}

} // verus!
