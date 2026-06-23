// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A2 "bv<->int / width casts (`as`)" (#1217, all green).
// Demonstrates: native `as_bv<w>` width-widening casts and `as_int` (bv->int)
// casts preserve the source `as` semantics end-to-end.
//
// NOTE: truncating casts (e.g. `300u32 as u8`) are omitted — Verus requires a
// `#[verifier::truncate]` acknowledgement and still does not fix the spec-level
// value, so they don't give a clean positive obligation here.
use vstd::prelude::*;

verus! {

// Width-widening cast u8 -> u32 (value preserved).
fn widen(x: u8) -> (r: u32)
    ensures r == x as u32,
{ x as u32 }

// Widening casts preserve the value on concrete operands.
proof fn widening_concrete() {
    assert(5u8 as u64 == 5);
    assert(255u8 as u32 == 255);
}

// bv -> int (`as_uint`): a u8 always lands in 0..256 as a mathematical int.
// (Casts are parenthesized before `<` so `int < N` is not read as `int<N>`.)
proof fn bv_to_int_bounds(x: u8) {
    assert(0 <= x as int);
    assert((x as int) < 256);
}

fn main() {}

} // verus!
