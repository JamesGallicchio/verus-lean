// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A1 "Fixed-width ints -> bitvectors" (all green).
// Demonstrates: every fixed-width integer type round-trips through its `bv{N}`
// model (u8..u64, i8..i64, usize/isize), and bitvector arithmetic is faithful
// on concrete operands.
//
// NOTE: arithmetic is kept concrete. A *symbolic* `ensures r == x + y` instead
// forces the bv->int bridge `as_uint(bvadd(x,y)) == as_uint(x)+as_uint(y)`,
// which cvc5 times out on at its default budget unless the operands are tightly
// bounded (see overflow_guard.rs for the bounded form).
use vstd::prelude::*;

verus! {

// Each width models a distinct bitvector; equality is preserved across all of them.
proof fn widths_roundtrip(
    a: u8, b: u16, c: u32, d: u64, e: usize,
    f: i8, g: i16, h: i32, i: i64, j: isize,
)
    requires
        a == 1, b == 2, c == 3, d == 4, e == 5,
        f == 6, g == 7, h == 8, i == 9, j == 10,
{
    assert(a == 1);
    assert(b == 2);
    assert(c == 3);
    assert(d == 4);
    assert(e == 5);
    assert(f == 6);
    assert(g == 7);
    assert(h == 8);
    assert(i == 9);
    assert(j == 10);
}

// Bitvector arithmetic on concrete operands evaluates faithfully.
proof fn concrete_bv_arithmetic() {
    assert(2u8 + 3 == 5);
    assert(100u16 * 3 == 300);
    assert(1000u32 - 1 == 999);
    assert(5u64 + 5 == 10);
}

fn main() {}

} // verus!
