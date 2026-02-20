#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn loop_simple(n: i32) -> i32
    requires n >= 0 && n <= 10000 // limit n to avoid overflow of `sum` or solver timeouts
{
    let mut sum: i32;
    let mut i: i32;

    sum = 0;
    i = 0;
    while i < n
        // invariant i <= n && (i * (i - 1)) / 2 == sum,
        // Without 0 <= i, Strata cannot show that the loop invariant maintains 
        // since i32 is not unbounded.
        invariant 0 <= i && i <= n && (i * (i - 1)) / 2 == sum,
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

/* program Boogie;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum));
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
 */
