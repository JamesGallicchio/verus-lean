// Mirrors verus/tests/LoopSimple.rs (the u32 version). The only deviation from the
// verus original is this import line: this toolchain links `vstd`, not the bare
// `builtin`/`builtin_macros` crates the verus repo's tests use.
use vstd::prelude::*;

verus! {

fn loop_simple(n: u32) -> u32
    requires n >= 0
{
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant i <= n && (i * (i - 1)) / 2 == sum,
        decreases n - i
    {
        sum = sum + i;
        i = i + 1;
    }
    assert((n * (n - 1)) / 2 == sum);
    assert(i == n);
    sum
}

fn main() {
}

} // verus!
