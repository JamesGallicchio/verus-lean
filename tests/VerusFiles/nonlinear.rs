use vstd::prelude::*;

verus! {

proof fn bound_check2(x: u32, y: u32, z: u32) by (lean)
    requires
        x <= 8,
        y <= 8,
    ensures
        x * y <= 64
{ }

proof fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int) by (lean)
    requires
        x <= x_bound,
        y <= y_bound,
        0 <= x,
        0 <= y,
    ensures
        x * y <= x_bound * y_bound,
{
}

proof fn lemma_mul_stay_positive(x: int, y: int) by (lean)
    requires
        0 <= x,
        0 <= y,
    ensures
        0 <= x * y,
{
}

proof fn lemma_inequality_after_mul(x: int, y: int, z: int) by (lean)
    requires
        x <= y,
        0 <= z,
    ensures
        x * z <= y * z,
{
}

proof fn lemma_div_pos_is_pos(x: int, d: int) by (lean)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= x / d,
{
}

proof fn wrong_lemma_1(x: int, y: int, z: int) by (lean)
    requires
        x <= y,
        0 <= z,
    ensures
        x * z < y * z, // FAILS
{
}

proof fn wrong_lemma_2(x: int, y: int, z: int) by (lean)
    requires
        x > y,
        3 <= z,
    ensures
        y * z > x, // FAILS
{
}

proof fn test5_bound_checking(x: u32, y: u32, z: u32) by (lean)
    requires
        x <= 0xffff,
        y <= 0xffff,
        z <= 0xffff,
    ensures
        0 <= x * z && x * z <= 0xffff * 0xffff
{
}

proof fn test6(x: u32, y: u32, z: u32) by (lean)
    requires x < 0xfff
    ensures 
        add(mul(x, x), x) == mul(x, add(x, 1)),
        mul(x, y) == mul(y, x),
{
}

proof fn test(x: nat, y: nat, z: nat) by (lean)
    requires x < 0xfff
    ensures x * x + x == x * (x + 1)
{
}

proof fn test7(x: int, y: int, z: int) {
    assert((x + y) * z == x * z + y * z) by(lean_proof as a0);
    assert((x - y) * z == x * z - y * z) by(lean_proof as a1);
}

proof fn test4_fails(x: u32, y: u32, z: u32) {
    assert(x * z == (mul(x, z) as int)) by(lean_proof as test4_a0); // should FAIL in Verus? currently will not fail in Lean
}

proof fn test_nonlinear(x: u32) by (lean)
    requires x < 0xfff
    ensures x * x + x == x * (x + 1)
{
}

proof fn test_negative(x: int, y: int, z:int) {
    assert((x + y) * z == x * z + y * z) by(lean_proof as test6_a0);
    assert(false) by(lean_proof as test6_a1); // FAILS
}

proof fn test_unexpected_vars(x: int, y: int, z:int) by (lean)
    requires
        y == 0,
        z == 0,
    ensures
        z == 0,
        x + y == x,
{
}

proof fn test_complex_vars(a1: int, a2: int) {
    assert({
        let (b1, b2) = if a1 <= a2 {
            (a1, a2)
        } else {
            (a2, a1)
        };
        b1 <= b2
    }) by (lean_proof as a1);
}


proof fn test_new_vars(x: int) by (lean)
    requires x == 5
    ensures x * 2 == 10
{
}

// Z3 is too slow with this test
proof fn test_nlarith1(x: int, y: int, z: int) by (lean)
    requires x * y == z && x != 0
    ensures z % x == 0
{
}

fn main() 
{}

}
