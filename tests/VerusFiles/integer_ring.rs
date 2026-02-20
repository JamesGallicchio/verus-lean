/* Adapted from source/rust_verify_test/tests/integer_ring.rs */
use vstd::prelude::*;

verus! {
    proof fn simple_1(x: int, y: int, z:int, m:int) by(lean)
        requires (x-y) % m == 0
        ensures (x*z - y*z) % m == 0
    {}

    proof fn simple_2(x: int, y: int, z:int) by(lean)
        ensures
            (x+y+z)*(x+y+z) == x*x + y*y + z*z + 2*(x*y + y*z + z*x)
    {}

    proof fn mont_mul_1(a:int, s:int, R:int, M:int, RR:int, R_INV:int) by(lean)
        requires
            (a * R - RR * s) % M == 0,
            (R_INV * R - 1) % M == 0,
            (RR - R * R % M) == 0,
        ensures
            (a - s*R) % M == 0
    {}

    proof fn mont_mul_2(p2_full: int, BASE: int, ui: int, m0: int, m0d: int, p1_lh: int, p1_full: int) by(lean)
        requires
            p2_full == ui * m0 + p1_lh,
            (p1_full - p1_lh) % BASE == 0,
            (m0d * m0 - (BASE-1)) % BASE == 0,
            (ui - p1_full * m0d) % BASE == 0,
        ensures
            p2_full % BASE == 0
    {}

    proof fn wide_mul(
        B: int,
        p0: int, p1: int, p2: int, p3: int,
        p4: int, p5: int, p6: int, p7: int,
        p8: int, p9: int, p10: int, p11: int,
        p12: int, p13: int, p14: int, p15: int,
        x: int, x_0: int, x_1: int, x_2: int, x_3: int,
        y: int, y_0: int, y_1: int,y_2: int, y_3: int) by(lean)

        requires
            x == x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B,
            y == y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B,
            p0 == x_0 * y_0,
            p1 == x_1 * y_0,
            p2 == x_0 * y_1,
            p3 == x_2 * y_0,
            p4 == x_1 * y_1,
            p5 == x_0 * y_2,
            p6 == x_3 * y_0,
            p7 == x_2 * y_1,
            p8 == x_1 * y_2,
            p9 == x_0 * y_3,
            p10 == x_3 * y_1,
            p11 == x_2 * y_2,
            p12 == x_1 * y_3,
            p13 == x_3 * y_2,
            p14 == x_2 * y_3,
            p15 == x_3 * y_3,
        ensures x * y == p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B + (p6 + p7 + p8 + p9) * B * B * B + (p10 + p11 + p12) * B * B * B * B + (p13 + p14) * B * B * B * B * B + p15 * B * B * B * B * B * B
    {}

    spec fn square(a:int) -> int{
        a*a
    }
    spec fn quad(a:int) -> int{
        a*a*a*a
    }
    proof fn test(x:int, y:int, m:int) by(lean) 
        requires
            (square(x) - square(y)) % m == 0,
            square(x) == x*x,
            square(y) == y*y,
            quad(x) == x*x*x*x,
            quad(y) == y*y*y*y,
        ensures (quad(x) - quad(y)) % m == 0
    {}

    // Failing test cases
    proof fn simple_fail_1(x: int, y: int, z:int, m:int) by(lean)
        requires
            (x-y) % m == 0
        ensures (x*z + y*z) % m == 0 //FAILS
    {}

    proof fn simple_fail_2(x: int, y: int, z:int) by(lean)
        ensures
            (x+y+z)*(x+y+z) == x*x + y*y + z + 2*(x*y + y*z + z*x) // FAILS
    {}

    proof fn wide_mul_fail(
        B: int,
        p0: int, p1: int, p2: int, p3: int,
        p4: int, p5: int, p6: int, p7: int,
        p8: int, p9: int, p10: int, p11: int,
        p12: int, p13: int, p14: int, p15: int,
        x: int, x_0: int, x_1: int, x_2: int, x_3: int,
        y: int, y_0: int, y_1: int,y_2: int, y_3: int) by(lean)

        requires
            x == x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B,
            y == y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B,
            p0 == x_0 * y_0,
            p1 == x_1 * y_0,
            p2 == x_0 * y_1,
            p3 == x_2 * y_0,
            p4 == x_1 * y_1,
            p5 == x_0 * y_2,
            p6 == x_3 * y_0,
            p7 == x_2 * y_2,   // originally  p7 == x_2 * y_1
            p8 == x_1 * y_2,
            p9 == x_0 * y_3,
            p10 == x_3 * y_1,
            p11 == x_2 * y_2,
            p12 == x_1 * y_3,
            p13 == x_3 * y_2,
            p14 == x_2 * y_3,
            p15 == x_3 * y_3,
        ensures x * y == p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B + (p6 + p7 + p8 + p9) * B * B * B + (p10 + p11 + p12) * B * B * B * B + (p13 + p14) * B * B * B * B * B + p15 * B * B * B * B * B * B // FAILS
    {}

    proof fn type_fail(x: u32, y: u32, z:u32, m:int) by(lean) // FAILS (not supported)
        requires
            (x-y) % m == 0
        ensures
            (x*z - y*z) % m == 0
    {}

    proof fn reserved_keyword(singular_tmp_1 : int, y: int, z:int, m:int) by(lean) // FAILS (not supported)
        requires (singular_tmp_1 - y) % m == 0
        ensures (singular_tmp_1 * z- y*z) % m == 0
    {}

    /* test_verify_one_file! {
        #[test]
        #[cfg_attr(not(feature = "singular"), ignore)]
        div_by_zero_fail verus_code! {
            proof fn may_div_zero(x : int) by(integer_ring)
                ensures x % x == 0
            {}

            proof fn div_by_zero_fails() {
                let a = 0int;
                may_div_zero(a);
                assert(a % a == 0); // FAILS , `x` shouldn't be zero
            }
        } => Err(err) => assert_one_fails(err)
    } */

    proof fn mul_mod_noop(x: int, y: int, m: int) by(lean)
        ensures
            ((x % m) * y) % m == (x * y) % m,
            (x * (y % m)) % m == (x * y) % m,
            ((x % m) * (y % m)) % m == (x * y) % m
    {}

    proof fn mul_mod_noop_fail_1(x: int, y: int, m: int) by(lean)
        ensures
            ((x % m) * y) % m == (x * y) % m,
            ((x % m) * (y % m)) % m == (x) % m, // FAILS
            (x * (y % m)) % m == (x * y) % m
    {}

    proof fn mul_mod_noop_fail_2(x: int, y: int, m: int) by(lean)
        ensures
            ((x % m) * y) % m == (x * y) % m,
            ((x % m) * (y % m)) % m == (x) % m, // FAILS
            (x * (y % m)) % m == (x) % m // also FAILS (but should not report this, since we stop at the first failure)
    {}

    proof fn neq_not_supported(x: int, y: int, z:int, m:int) by(lean)
        requires (x-y) % m != 0  //FAILS (not supported)
        ensures (x*z + y*z) % m == 0
    {}

    proof fn gt_not_supported(x: int, y: int, z:int, m:int) by(lean)
        requires (x-y) % m > 0  //FAILS (not supported)
        ensures (x*z + y*z) % m == 0
    {}

    proof fn lt_not_supported(x: int, y: int, z:int, m:int) by(lean)
        requires (x-y) % m == 0
        ensures (x*z + y*z) % m < 0 //FAILS (not supported)
    {}

   pub proof fn mod_trans(a: int, b: int, c: int) by(lean)
        requires /*b != 0, c != 0,*/ a % b == 0, b % c == 0,
        ensures a % c == 0
    {
    }

    fn main()
    {}

}
