#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

  enum Sport {
    Soccer { num_players: nat, team_id: int },
    Running { distance: nat },
    Swimming { num_laps: nat, is_relay : bool },
  }

  enum NatBox {
    Nat(nat),
  }

  use crate::Sport::*;
  use crate::NatBox::*;

  spec fn sport_nat(s: Sport) -> nat
  {
    match s {
      Soccer { num_players, team_id } => num_players,
      Running { distance } => distance,
      Swimming { num_laps, is_relay } => num_laps,
    }
  }

  spec fn get_data_in_box(b: NatBox) -> nat
  {
    match b {
      Nat(n) => n,
    }
  }

  proof fn req_ens(s: Sport)
  {
    assert(sport_nat(s) >= 0) by (lean_proof as a1);
  }

  proof fn box_test(b : NatBox)
  {
    assert(get_data_in_box(b) >= 0) by (lean_proof as a1);
  }

  proof fn test_is_operator(s: Sport)
  {
    assert(s is Soccer) by (lean_proof as a1);
  }

/* Example to demonstrate an issue with enum field access when translated to Lean */
  enum Life {
    Mammal { legs: int, has_pocket: bool },
    Arthropod { legs: int, wings: int },
    Plant { leaves: int },
  }

  spec fn is_insect(l: Life) -> int
  {
      l->Arthropod_legs
  }

  proof fn is_insect_proof()
  {
    let l = Life::Mammal { legs: 0, has_pocket: true };
    assert(is_insect(l) == 6) by (lean_proof as a1);
  }

  fn main() 
  {
  }
}
