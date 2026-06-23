// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A1 "Bitwise ops on bvN (& | ^ << >> >>s ~)" (#970, all green).
// Demonstrates: the unsigned bitvector bitwise operators lower to native
// Boole/Core bv ops and the resulting obligations discharge in Strata via cvc5's
// bv theory.
//
// Each assert uses `by (lean)`: Verus's *default* arithmetic solver treats
// integer bitwise ops as opaque (so a plain `assert` fails in Verus), and
// `by (bit_vector)` would route to Strata's `[bitvector_query]` dispatch, which
// is incomplete. `by (lean)` instead emits the real `as_uint(a & b) == ...`
// obligation, which Strata/cvc5 discharges. Each `&`/`|`/`^` is parenthesized
// because Rust binds those below `==`.
//
// CAVEAT (matrix over-claims `>>s`): the signed/arithmetic right shift `>>s` is
// NOT supported end-to-end — on a negative literal the translator emits malformed
// Boole ("bv32 when int expected"), and on an i32 variable it lowers to
// `Bv32.SShr`, undeclared in Strata Core. So `>>s` is omitted; the other six
// operators (& | ^ << >> ~) are exercised below.
use vstd::prelude::*;

verus! {

proof fn bitwise_unsigned() {
    assert((0xF0u32 & 0x0F) == 0x00) by (lean);   // and
    assert((0xF0u32 | 0x0F) == 0xFF) by (lean);   // or
    assert((0xFFu32 ^ 0x0F) == 0xF0) by (lean);   // xor
    assert((!0u32) == 0xFFFF_FFFF) by (lean);     // not
    assert((1u32 << 4) == 16) by (lean);          // left shift
    assert((0x80u32 >> 3) == 0x10) by (lean);     // unsigned (logical) right shift
}

fn main() {}

} // verus!
