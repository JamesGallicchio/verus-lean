use vstd::prelude::*;

verus! {

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn mult_two(i: int) -> int {
  i * 2
}

spec fn add(x: int, y: int) -> int {
  x + y
}

spec fn not_asserted(x: int) -> int by (lean_proof) {
  x + 3
}

proof fn assert_add_one(i: int)
{
  assert(add_one(i) == i + 1) by (lean_proof as a1);
  assert(add_one(i + 1) == i + 2) by (lean_proof as a2);
  assert(add_one(i) + 1 == i + 2) by (lean_proof as a3);
}

proof fn assert_mult_two(i: int)
{
  assert(mult_two(i) == i * 2) by (lean_proof as a1);
  assert(mult_two(i + 1) == i * 2 + 2) by (lean_proof as a2);
  assert(mult_two(i) + 1 == i * 2 + 1) by (lean_proof as a3);
}

proof fn assert_add(x: int, y: int)
{
  assert(add(x, y) == x + y) by (lean_proof as a1);
  assert(add(x, y) == add(y, x)) by (lean_proof as a2);
  assert(add(x, 1) == add_one(x)) by (lean_proof as a3);
}

fn main()
{}

}
