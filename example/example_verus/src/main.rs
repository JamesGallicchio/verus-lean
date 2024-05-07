use vstd::prelude::*;

verus!{

spec fn test(x: int) -> bool
//ensures (y.is_some())
{
    test2(x+1)
}

spec fn test2(x: int) -> bool
//ensures (y.is_some())
{
    test(x+1)
}

pub fn main() -> (x : Result<(),u32>)
ensures true
{
    if [1,2,3][2] == [3,4,5][0] {
        return Ok(());
    } else {
        return Err(0);
    }
}

}
