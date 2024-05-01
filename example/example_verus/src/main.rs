use vstd::prelude::*;

verus!{

pub fn test(x: int) -> ()
requires (x == x)
//ensures (y.is_some())
{
    return ();
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
