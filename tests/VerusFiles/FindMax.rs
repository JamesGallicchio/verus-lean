/* Finds and returns the largest integer in a non-empty vector by iterating through its elements. */
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn find_max(nums: Vec<i32>) -> (ret:i32)
    requires
        nums.len() > 0
    ensures
        forall|i: int| 0 <= i && i < nums.len() ==> ret >= nums[i],
        exists|j: int| 0 <= j && j < nums.len() && ret == nums[j]
{
    let mut max = nums[0];
    let mut i = 1;

    while i < nums.len()
        invariant
            nums.len() > 0,
            0 <= i && i <= nums.len(),
            forall|k: int| 0 <= k && k < i ==> max >= nums[k],
            exists|j: int| 0 <= j && j < i && max == nums[j]
        decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }

    max
}
}
