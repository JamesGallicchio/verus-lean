use vstd::prelude::*;

verus! {

proof fn simple_forall(i: int) {
  // global variable, bound by function
  assert(i != i + 1) by (lean_proof as a1);
  // simple forall statement
  assert(forall|x:int| x != #[trigger] (x + 1)) by (lean_proof as a2);
  // double forall statement
  assert(forall|x:int, y:nat| x + y == #[trigger] (y + x)) by (lean_proof as a3);
  // refer to global variable inside the body
  assert(forall|x:int, y:nat| x + y + i != #[trigger] (x + y + i + 1)) by (lean_proof as a4);
}

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn add(x: int, y: int) -> int {
  x + y
}

proof fn forall_with_specfn(i: int) {
  // standard commutativity
  assert(forall|x:int, y:int| add(x, y) == add(y, x)) by (lean_proof as a1);
  // assert(forall|x:int, y:int| add(y, x) == add(x, y)) by (lean_proof as a1);
  // shadowing
  assert(forall|i:int| 0 <= i <= 10 ==> add_one(i) == i + 1) by (lean_proof as a2);
}

proof fn simple_exists() {
  assert(exists|x:int| x != #[trigger] (x + 1)) by (lean_proof as ne_succ);
}

fn main() {
}

}
