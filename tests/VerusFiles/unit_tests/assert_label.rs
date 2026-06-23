// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B4 "assert(P) by (... as <name>) labels"
// ([TRANS-assert-label], RESOLVED 2026-06-22, all green).
// Demonstrates: a source `by (lean_proof as <name>)` label is preserved through
// to a named Boole obligation `assert [<name>]: P;`.
use vstd::prelude::*;

verus! {

spec fn add1(i: int) -> int { i + 1 }

proof fn labeled_asserts(i: int) {
    assert(add1(i) == i + 1) by (lean_proof as a1);
    assert(add1(i + 1) == i + 2) by (lean_proof as a2);
    assert(add1(add1(i)) == i + 2) by (lean_proof as a3);
}

fn main() {}

} // verus!
