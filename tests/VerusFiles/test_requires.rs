use vstd::prelude::*;

verus! {

fn test_success(x: u32, y: u32)
requires
    x == y,
{
  assert(x & 3 == y & 3) by (bit_vector)
      requires
          x == y,
  ;  // now x == y is available for the bit_vector proof
}

proof fn bound_check(x: u32, y: u32, z: u32)
    requires
        x <= 8,
        y <= 8,
{
    assert(x * y <= 100) by (nonlinear_arith)
    // assert(x * y <= 100) by (lean)
        requires
            x <= 10,
            y <= 10;

    assert(x * y <= 1000);
}

fn main() {
}

}
