import Mathlib
import VerusLean.VerusAesopSetup

abbrev math.add (x y : Int) := x + y
abbrev math.sub (x y : Int) := x - y

noncomputable def undefined [Nonempty α] : α := Classical.choice inferInstance

class Clip (_from : Type u) (_to : Type v) where
  clip : (x : _from) → _to

attribute [simp] Clip.clip

@[simp]
def clip {_from : Type u} (_to : Type v) [Clip _from _to] (x : _from) : _to :=
  Clip.clip x

instance : Clip Nat Nat where
  clip := id

instance : Clip Int Nat where
  clip := Int.natAbs

@[elab_as_elim]
theorem Int.natAbs_elim {motive : Nat → Prop} {i : Int} (x : Nat)
  (hi : Int.natAbs i = x)
  (hpos : ∀ (n : Nat), i = n → motive n)
  (hneg : ∀ (n : Nat), i = -↑n → motive n)
  : motive x := by
  cases i <;> aesop
  apply hneg
  simp [Int.negSucc_eq]

elab "tactic_natAbs_elim_error_if_type_has_mvar" e:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
  let e ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm e none)
  let ty ← Lean.Meta.inferType e
  if ty.hasMVar then
    throwError s!"type {ty} has mvar"

@[aesop safe 100 tactic (rule_sets := [VerusLean])]
def Int.tactic_natAbs_elim : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    generalize h : Int.natAbs _ = n
    tactic_natAbs_elim_error_if_type_has_mvar h
    refine Int.natAbs_elim n h ?_ ?_ <;> cases h
  )
  ))

@[aesop safe 1000 tactic (rule_sets := [VerusLean])]
def evalLinarith : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    linarith
  ))

attribute [aesop unsafe 1% apply (rule_sets := [VerusLean])]
  Int.ediv_eq_zero_of_lt
  Int.emod_eq_of_lt
  Int.emod_nonneg
  Int.emod_lt_of_pos
  Int.mul_assoc

attribute [aesop norm simp (rule_sets := [VerusLean])]
  Int.ediv_add_emod
  Int.div_nonneg_iff_of_pos
