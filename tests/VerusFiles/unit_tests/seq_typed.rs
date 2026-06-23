// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B3 "Typed seq literals/empty
// (Sequence.of_bv8, Sequence.empty_bv8)" ([SURFACE-sequence-empty], all green).
// Demonstrates: a concrete-element-typed `Seq<u8>` literal and a typed empty
// `Seq<u8>` encode end-to-end (Sequence.of_bv8 / Sequence.empty_bv8), with
// length and concrete-index access.
use vstd::prelude::*;

verus! {

proof fn typed_seq() {
    let s: Seq<u8> = seq![1u8, 2u8, 3u8]; // Sequence.of_bv8
    assert(s.len() == 3);
    assert(s[0] == 1);
    assert(s[2] == 3);

    let e: Seq<u8> = Seq::<u8>::empty(); // Sequence.empty_bv8
    assert(e.len() == 0);
}

fn main() {}

} // verus!
