// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A2 "usize/isize loop counters as seq indices"
// ([TRANS-loop-counter-int], all green).
// Demonstrates: a `usize` loop counter used to index a fixed-size array is
// promoted to `int`, so `a[i]` and its in-bounds check discharge end-to-end.
// This mirrors the exact shape that makes sha256 green: a `for i in 0..N`
// range loop over a *local* fixed array, whose length/bounds facts the
// for-range recovery path supplies. (A hand-rolled `while` loop, or indexing a
// symbolic array *parameter*, instead leaves `Sequence.length(a)` opaque and
// pushes the `Sequence.select` in-bounds obligation into the cvc5-unknown
// Seq-frontend gap — so this stays in the `for`-over-local form on purpose.)
use vstd::prelude::*;

verus! {

fn scan() -> (last: u32) {
    let a: [u32; 4] = [5, 6, 7, 8];
    let mut last: u32 = 0;
    for i in 0..4 {
        last = a[i]; // `usize` counter `i` indexes the array (promoted to int)
    }
    last
}

fn main() {}

} // verus!
