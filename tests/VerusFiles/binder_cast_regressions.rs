use vstd::prelude::*;

verus! {

proof fn binder_shadowing_and_order(outer: int) {
    assert(forall|x: int, y: int| #[trigger] (x + y) == y + x) by (lean_proof as comm);
    assert(forall|outer: int| #[trigger] (outer + 1) == 1 + outer) by (lean_proof as shadow);
}

proof fn quantified_int_against_usize(n: usize) {
    assert(forall|i: int| 0 <= i && i < n ==> #[trigger] (i + 1) <= n + 1) by (lean_proof as mixed);
}

proof fn nested_mixed_int_usize_arith(n: usize) {
    assert(forall|i: int| 0 <= i ==> #[trigger] ((i + 1) + n) == (n + (i + 1))) by (lean_proof as nested_mixed);
}

fn main() {
}

} // verus!
