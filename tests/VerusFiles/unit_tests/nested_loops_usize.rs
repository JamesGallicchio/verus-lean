// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// Companion to nested_loops.rs, which uses `u32` counters and so never reaches
// `IntPromotion`.  Here both counters are `usize` used as sequence indices, so
// both are retyped to `Int` and both qualify for the synthesized
// non-negativity invariant.
//
// The inner counter `j` is declared inside the outer body, so it holds no value
// at the outer loop's entry.  A synthesized `0 <= j` on the *outer* loop would
// therefore be an entry obligation about an uninitialized variable — provable
// nowhere.  Each counter's invariant must land on its own loop.
use vstd::prelude::*;

verus! {

fn nested_usize(s: Vec<u64>)
    requires s.len() == 1,
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
        decreases s.len() - i,
    {
        let ghost _a = s[i as int];
        let mut j: usize = 0;
        while j < s.len()
            invariant
                0 <= j,
                j <= s.len(),
            decreases s.len() - j,
        {
            let ghost _b = s[j as int];
            j = j + 1;
        }
        i = i + 1;
    }
}

fn main() {}

} // verus!
