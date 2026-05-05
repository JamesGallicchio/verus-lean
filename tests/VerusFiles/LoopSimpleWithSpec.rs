#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;

verus! {

spec fn triangle0(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        ((n - 1) as nat) + triangle0((n - 1) as nat)
    }
}

proof fn triangle0_is_monotonic(i: nat, j: nat) by (lean)
    requires
        i <= j,
    ensures
        triangle0(i) <= triangle0(j),
{
}

fn loop_simple(n: u32) -> u32
    requires triangle0(n as nat) < 0x1_0000_0000,
{
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            sum == triangle0(i as nat),
            triangle0(n as nat) < 0x1_0000_0000,
        decreases n - i
    {
        i = i + 1;
        assert(sum + (i - 1) < 0x1_0000_0000) by {
            triangle0_is_monotonic(i as nat, n as nat);
        }
        sum = sum + (i - 1);
    }
    assert(sum == triangle0(n as nat));
    assert(i == n);
    sum
}

fn main() {
}

} // verus!

/* program Boogie;

function triangle0(n: int) returns (int);

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (triangle0(n) < 0x1_0000_0000);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && sum == triangle0(i) && triangle0(n) < 0x1_0000_0000);
  {
    i := i + 1;
    sum := sum + (i - 1);
  }
  assert [sum_assert]: (sum == triangle0(n));
  assert [neg_cond]: (i == n);
  r := sum;
};
 */
