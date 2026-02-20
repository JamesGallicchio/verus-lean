use vstd::prelude::*;

verus! {

proof fn assert_lean_array(x: [u32; 3]) {
  let a: [u32; 3] = [3, 3, 0];
  let b: [u32; 3] = [3, 3, 1];
  assert(a != b) by (lean);
}

fn main() {}

}
