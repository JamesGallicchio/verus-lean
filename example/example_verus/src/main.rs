use vstd::prelude::*;

verus!{

pub fn test(x: u32) -> (y : Option<u32>)
requires (x < 20 && x > 1)
//ensures (y.is_some())
{
    return x.checked_add(1);
}

pub fn main() -> (x : Result<(),i32>)
ensures true
{
    if [1,2,3][2] == [3,4,5][0] {
        return Ok(());
    } else {
        return Err(0);
    }
}

}
