import Mathlib

abbrev math.add (x y : Int) := x + y
abbrev math.sub (x y : Int) := x - y

macro "verus_default_tac" : tactic =>
  `(tactic| first | (aesop <;> sorry) | sorry)

noncomputable def undefined [Nonempty α] : α := Classical.choice inferInstance

class Clip (_from : Type u) (_to : Type v) where
  clip : (x : _from) → _to

def clip {_from : Type u} (_to : Type v) [Clip _from _to] (x : _from) : _to :=
  Clip.clip x

instance : Clip Nat Nat where
  clip := id

instance : Clip Int Nat where
  clip := Int.natAbs
