/* Adapted from source/rust_verify_test/tests/vec.rs::test_vec_into_iter */

use vstd::prelude::*;
use vstd::std_specs::vec::*;

verus! {

fn test_vec_ops() {
    let mut v1: Vec<u32> = Vec::new();
    let mut v2: Vec<u32> = Vec::new();
    v1.push(3);
    v1.push(4);
    assert(v1@ == seq![3u32, 4u32]);

    v2.push(5);
    assert(v2.len() == 1);
    v2.push(7);
    assert(v2@.len() == 2);
    v2.insert(1, 6);
    assert(v2@ == seq![5u32, 6u32, 7u32]);

    v1.append(&mut v2);
    assert(v2@.len() == 0);
    assert(v1@.len() == 5);
    assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
    v1.remove(2);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

    v1.push(8u32);
    v1.push(9u32);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

    v1.swap_remove(5);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);
}

} // verus!
fn main() {}
