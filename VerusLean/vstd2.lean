import VerusLean.Macro
import VerusLean.VerusBuiltins

namespace VerusLean

open Macro

noncomputable section
open Classical

set_option linter.unusedVariables false

-- #generate_verus_funcs ↑"verus/source/vstd.json" {{}}

def vstd.arithmetic.internals.general_internals.is_le (x : Int) (y : Int) : Bool :=
  x ≤ y

def vstd.arithmetic.internals.mod_internals_nonlinear.modulus (x : Int) (y : Int) : Int :=
  x % y

def vstd.arithmetic.internals.div_internals.div_pos (x : Int) (d : Int) : Int :=
  if d > 0 then
    if x < 0 then 0 - 1 + vstd.arithmetic.internals.div_internals.div_pos (x + d) d
    else if x < d then 0 else 1 + vstd.arithmetic.internals.div_internals.div_pos (x - d) d
  else undefined
termination_by Int.natAbs (if x < 0 then d - x else x)
decreasing_by all_goals (simp_wf; aesop (rule_sets := [VerusLean]))

def vstd.arithmetic.internals.div_internals.div_recursive (x : Int) (d : Int) : Int :=
  if d > 0 then vstd.arithmetic.internals.div_internals.div_pos x d
  else (0 - 1) * vstd.arithmetic.internals.div_internals.div_pos x ((0 - 1) * d)

def vstd.arithmetic.internals.div_internals.div_auto_plus (n : Int) : Bool :=
  ∀ (x : Int) (y : Int),
    let z := x % n + y % n;
    (0 ≤ z ∧ z < n) ∧ (x + y) / n = x / n + y / n ∨ (n ≤ z ∧ z < n + n) ∧ (x + y) / n = x / n + y / n + 1

def vstd.arithmetic.internals.div_internals.div_auto_minus (n : Int) : Bool :=
  ∀ (x : Int) (y : Int),
    let z := x % n - y % n;
    (0 ≤ z ∧ z < n) ∧ (x - y) / n = x / n - y / n ∨ (0 - n ≤ z ∧ z < 0) ∧ (x - y) / n = x / n - y / n - 1

def vstd.arithmetic.internals.mod_internals.mod_auto_plus (n : Int) : Bool :=
  ∀ (x : Int) (y : Int),
    let z := x % n + y % n;
    (0 ≤ z ∧ z < n) ∧ (x + y) % n = z ∨ (n ≤ z ∧ z < n + n) ∧ (x + y) % n = z - n

def vstd.arithmetic.internals.mod_internals.mod_auto_minus (n : Int) : Bool :=
  ∀ (x : Int) (y : Int),
    let z := x % n - y % n;
    (0 ≤ z ∧ z < n) ∧ (x - y) % n = z ∨ (0 - n ≤ z ∧ z < 0) ∧ (x - y) % n = z + n

def vstd.arithmetic.internals.mod_internals.mod_auto (n : Int) : Bool :=
  ((((n % n = 0 ∧ (0 - n) % n = 0) ∧ ∀ (x : Int), x % n % n = x % n) ∧ ∀ (x : Int), (0 ≤ x ∧ x < n) = (x % n = x)) ∧
      vstd.arithmetic.internals.mod_internals.mod_auto_plus n) ∧
    vstd.arithmetic.internals.mod_internals.mod_auto_minus n

def vstd.arithmetic.internals.div_internals.div_auto (n : Int) : Bool :=
  (((vstd.arithmetic.internals.mod_internals.mod_auto n ∧
          let «tmp%%» := 0 - (0 - n) / n;
          n / n = «tmp%%» ∧ «tmp%%» = 1) ∧
        ∀ (x : Int), (0 ≤ x ∧ x < n) = (x / n = 0)) ∧
      vstd.arithmetic.internals.div_internals.div_auto_plus n) ∧
    vstd.arithmetic.internals.div_internals.div_auto_minus n

def vstd.arithmetic.internals.mod_internals.mod_recursive (x : Int) (d : Int) : Int :=
  if d > 0 then
    if x < 0 then vstd.arithmetic.internals.mod_internals.mod_recursive (d + x) d
    else if x < d then x else vstd.arithmetic.internals.mod_internals.mod_recursive (x - d) d
  else undefined
termination_by Int.natAbs (if x < 0 then d - x else x)
decreasing_by all_goals (simp_wf; aesop (rule_sets := [VerusLean]))

def vstd.arithmetic.internals.mul_internals.mul_pos (x : Int) (y : Int) : Int :=
  if x ≤ 0 then 0 else y + vstd.arithmetic.internals.mul_internals.mul_pos (x - 1) y
termination_by Int.natAbs x
decreasing_by all_goals (simp_wf; aesop (rule_sets := [VerusLean]))

def vstd.arithmetic.internals.mul_internals.mul_recursive (x : Int) (y : Int) : Int :=
  if x ≥ 0 then vstd.arithmetic.internals.mul_internals.mul_pos x y
  else (0 - 1) * vstd.arithmetic.internals.mul_internals.mul_pos ((0 - 1) * x) y

def vstd.arithmetic.internals.mul_internals.mul_auto («no%param» : Int) : Bool :=
  ((∀ (x : Int) (y : Int), x * y = y * x) ∧ ∀ (x : Int) (y : Int) (z : Int), (x + y) * z = x * z + y * z) ∧
    ∀ (x : Int) (y : Int) (z : Int), (x - y) * z = x * z - y * z

def vstd.arithmetic.div_mod.is_mod_equivalent (x : Int) (y : Int) (m : Int) : Bool :=
  (x % m = y % m) = ((x - y) % m = 0)

def vstd.arithmetic.logarithm.log (base : Int) (pow : Int) : Int :=
  if (pow < base ∨ pow / base ≥ pow) ∨ pow / base < 0 then 0 else 1 + vstd.arithmetic.logarithm.log base (pow / base)
termination_by Int.natAbs pow
decreasing_by all_goals (simp_wf; aesop (rule_sets := [VerusLean]))

def vstd.arithmetic.power.pow (b : Int) (e : Nat) : Int :=
  if e = 0 then 1 else b * vstd.arithmetic.power.pow b (Int.natAbs (e - 1))
termination_by Int.natAbs e
decreasing_by all_goals (simp_wf; aesop (rule_sets := [VerusLean]))

def vstd.arithmetic.power2.pow2 (e : Nat) : Nat :=
  Int.natAbs (vstd.arithmetic.power.pow 2 e)

theorem vstd.arithmetic.internals.div_internals_nonlinear.lemma_div_of0 (d : Int) : !d = 0 → 0 / d = 0 := by
  simp

theorem vstd.arithmetic.internals.div_internals_nonlinear.lemma_div_by_self (d : Int) : !d = 0 → d / d = 1 := by
  simp_all

theorem vstd.arithmetic.internals.div_internals_nonlinear.lemma_small_div («no%param» : Int) :
    ∀ (x : Int) (d : Int), (0 ≤ x ∧ x < d) ∧ d > 0 → x / d = 0 := by
  intro a b h; rcases h with ⟨⟨h1,h2⟩,h3⟩; exact Int.ediv_eq_zero_of_lt h1 h2

theorem vstd.arithmetic.internals.general_internals.lemma_induction_helper_pos (n : Int) (f : Int → Bool) (x : Int) :
    x ≥ 0 →
      n > 0 →
        (∀ (i : Int), 0 ≤ i ∧ i < n → f i) →
          (∀ (i : Int), i ≥ 0 ∧ f i → f (vstd.math.add i n)) →
            (∀ (i : Int), i < n ∧ f i → f (vstd.math.sub i n)) → f x := by
  intro h1 h2 h3 h4 h5
  have : x = x.natAbs := Int.eq_natAbs_of_zero_le h1
  generalize x.natAbs = x' at this
  subst this; clear h1
  have : n = n.natAbs := Int.eq_natAbs_of_zero_le (by omega)
  generalize n.natAbs = n at *
  subst this
  induction x' using Nat.strongInductionOn with
  | ind x ih =>
  if x < n then
    simp_all
  else
    have : x = (x - n) + n := by omega
    rw [this, Int.ofNat_add]
    apply h4
    constructor
    · omega
    · apply ih
      omega


theorem vstd.arithmetic.internals.general_internals.lemma_induction_helper_neg (n : Int) (f : Int → Bool) (x : Int) :
    x < 0 →
      n > 0 →
        (∀ (i : Int), 0 ≤ i ∧ i < n → f i) →
          (∀ (i : Int), i ≥ 0 ∧ f i → f (vstd.math.add i n)) →
            (∀ (i : Int), i < n ∧ f i → f (vstd.math.sub i n)) → f x := by
  intro h1 h2 h3 h4 h5
  have : -x = (-x).natAbs := Int.eq_natAbs_of_zero_le (by omega)
  generalize (-x).natAbs = x' at this
  rw [Int.neg_eq_comm, eq_comm] at this
  subst this; clear h1
  have : n = n.natAbs := Int.eq_natAbs_of_zero_le (by omega)
  generalize n.natAbs = n at *
  subst this
  induction x' using Nat.strongInductionOn with
  | ind x ih =>
  if x = 0 then
    apply h3; simp [*]
  else
    if x ≤ n then
      have : -(x : Int) = (n - x) - n := by omega
      rw [this]
      apply h5
      constructor
      · omega
      apply h3; constructor <;> omega
    else
      have : -(x : Int) = -((x-n : Nat) : Int) - n := by omega
      rw [this]
      apply h5
      constructor
      · omega
      · apply ih
        omega


theorem vstd.arithmetic.internals.general_internals.lemma_induction_helper (n : Int) (f : Int → Bool) (x : Int) :
    n > 0 →
      (∀ (i : Int), 0 ≤ i ∧ i < n → f i) →
        (∀ (i : Int), i ≥ 0 ∧ f i → f (vstd.math.add i n)) →
          (∀ (i : Int), i < n ∧ f i → f (vstd.math.sub i n)) → f x := by
  intros
  if h : x < 0 then
    apply lemma_induction_helper_neg n f x h <;> assumption
  else
    apply lemma_induction_helper_pos n f x (by omega) <;> assumption

theorem vstd.arithmetic.internals.mod_internals_nonlinear.lemma_mod_of_zero_is_zero (m : Int) : 0 < m → 0 % m = 0 :=
  by intros; aesop

theorem vstd.arithmetic.internals.mod_internals_nonlinear.lemma_fundamental_div_mod (x : Int) (d : Int) :
    !d = 0 → x = d * (x / d) + x % d :=
  by intros; simp_all; exact Eq.symm (Int.ediv_add_emod x d)

theorem vstd.arithmetic.internals.mod_internals_nonlinear.lemma_0_mod_anything («no%param» : Int) :
    ∀ (m : Int), m > 0 → vstd.arithmetic.internals.mod_internals_nonlinear.modulus 0 m = 0 :=
  by intro m h; aesop

theorem vstd.arithmetic.internals.mod_internals_nonlinear.lemma_small_mod (x : Nat) (m : Nat) :
    x < m → 0 < m → vstd.arithmetic.internals.mod_internals_nonlinear.modulus x m = x :=
  by intros; simp [modulus]; apply Int.emod_eq_of_lt <;> aesop

theorem vstd.arithmetic.internals.mod_internals_nonlinear.lemma_mod_range (x : Int) (m : Int) :
    m > 0 →
      let «tmp%%» := vstd.arithmetic.internals.mod_internals_nonlinear.modulus x m;
      0 ≤ «tmp%%» ∧ «tmp%%» < m := by
  intro h; simp [modulus]; constructor
  · apply Int.emod_nonneg x; aesop
  · exact Int.emod_lt_of_pos x h

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_strictly_positive (x : Int) (y : Int) :
    0 < x ∧ 0 < y → 0 < x * y := by
  rintro ⟨h1,h2⟩; exact Int.mul_pos h1 h2

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_nonzero (x : Int) (y : Int) :
    (!x * y = 0) = (!x = 0 ∧ !y = 0) := by
  simp

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_is_associative (x : Int) (y : Int) (z : Int) :
    x * (y * z) = x * y * z := by
  ring

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_is_distributive_add (x : Int) (y : Int)
    (z : Int) : x * (y + z) = x * y + x * z := by
  ring

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_ordering (x : Int) (y : Int) :
    !x = 0 → !y = 0 → 0 ≤ x * y → x * y ≥ x ∧ x * y ≥ y := by
  intros; simp_all
  have : x * y ≠ 0 := by intro h; rw [mul_eq_zero] at h; simp_all
  have : x * y > 0 := by omega
  if y < 0 then
    have : x ≤ 0 := by apply nonpos_of_mul_nonneg_left <;> assumption
    have : x < 0 := by omega
    constructor <;> omega
  else
    have : y > 0 := by omega
    have : x > 0 := by apply pos_of_mul_pos_left; assumption; omega
    constructor
    · rw [le_mul_iff_one_le_right] <;> assumption
    · rw [le_mul_iff_one_le_left] <;> assumption

theorem vstd.arithmetic.internals.mul_internals_nonlinear.lemma_mul_strict_inequality (x : Int) (y : Int) (z : Int) :
    x < y → z > 0 → x * z < y * z := by
  aesop

theorem vstd.arithmetic.mul.lemma_mul_is_commutative (x : Int) (y : Int) : x * y = y * x := by
  aesop

theorem vstd.arithmetic.mul.lemma_mul_is_distributive_add (x : Int) (y : Int) (z : Int) :
    x * (y + z) = x * y + x * z := by
  exact internals.mul_internals_nonlinear.lemma_mul_is_distributive_add x y z

theorem vstd.arithmetic.internals.mul_internals.lemma_mul_commutes (x : Int) (y : Int) : x * y = y * x := by
  aesop

theorem vstd.arithmetic.internals.mul_internals.lemma_mul_successor («no%param» : Int) :
    (∀ (x : Int) (y : Int), (x + 1) * y = x * y + y) ∧ ∀ (x : Int) (y : Int), (x - 1) * y = x * y - y := by
  aesop

theorem vstd.arithmetic.internals.mul_internals.lemma_mul_induction (f : Int → Bool) :
    f 0 →
      (∀ (i : Int), i ≥ 0 ∧ f i → f (vstd.math.add i 1)) →
        (∀ (i : Int), i ≤ 0 ∧ f i → f (vstd.math.sub i 1)) → ∀ (i : Int), f i := by
  aesop

theorem vstd.arithmetic.internals.mul_internals.lemma_mul_distributes_plus (x : Int) (y : Int) (z : Int) :
    (x + y) * z = x * z + y * z :=
  sorry
theorem vstd.arithmetic.internals.mul_internals.lemma_mul_distributes_minus (x : Int) (y : Int) (z : Int) :
    (x - y) * z = x * z - y * z :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_distributive_add_other_way (x : Int) (y : Int) (z : Int) :
    (y + z) * x = y * x + z * x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_distributive_sub (x : Int) (y : Int) (z : Int) :
    x * (y - z) = x * y - x * z :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_distributive_sub_other_way (x : Int) (y : Int) (z : Int) :
    (y - z) * x = y * x - z * x :=
  sorry
theorem vstd.arithmetic.internals.mul_internals.lemma_mul_induction_auto (x : Int) (f : Int → Bool) :
    (vstd.arithmetic.internals.mul_internals.mul_auto 0 →
        (f 0 ∧ ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + 1)) ∧
          ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le i 0 ∧ f i → f (i - 1)) →
      vstd.arithmetic.internals.mul_internals.mul_auto 0 ∧ f x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_inequality (x : Int) (y : Int) (z : Int) : x ≤ y → z ≥ 0 → x * z ≤ y * z :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_add_denominator (n : Int) (x : Int) :
    n > 0 → (x + n) % n = x % n :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_sub_denominator (n : Int) (x : Int) :
    n > 0 → (x - n) % n = x % n :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_div_add_denominator (n : Int) (x : Int) :
    n > 0 → (x + n) / n = x / n + 1 :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_div_sub_denominator (n : Int) (x : Int) :
    n > 0 → (x - n) / n = x / n - 1 :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_below_denominator (n : Int) (x : Int) :
    n > 0 → (0 ≤ x ∧ x < n) = (x % n = x) :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_basics (n : Int) :
    n > 0 →
      (∀ (x : Int), (x + n) % n = x % n) ∧
        (∀ (x : Int), (x - n) % n = x % n) ∧
          (∀ (x : Int), (x + n) / n = x / n + 1) ∧
            (∀ (x : Int), (x - n) / n = x / n - 1) ∧ ∀ (x : Int), (0 ≤ x ∧ x < n) = (x % n = x) :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_quotient_and_remainder (x : Int) (q : Int) (r : Int) (n : Int) :
    n > 0 → 0 ≤ r ∧ r < n → x = q * n + r → q = x / n ∧ r = x % n :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_auto (n : Int) :
    n > 0 → vstd.arithmetic.internals.mod_internals.mod_auto n :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_basics (n : Int) :
    n > 0 →
      (n / n = 1 ∧ 0 - (0 - n) / n = 1) ∧
        (∀ (x : Int), (0 ≤ x ∧ x < n) = (x / n = 0)) ∧
          (∀ (x : Int), (x + n) / n = x / n + 1) ∧ ∀ (x : Int), (x - n) / n = x / n - 1 :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_induction_forall (n : Int) (f : Int → Bool) :
    n > 0 →
      (∀ (i : Int), 0 ≤ i ∧ i < n → f i) →
        (∀ (i : Int), i ≥ 0 ∧ f i → f (vstd.math.add i n)) →
          (∀ (i : Int), i < n ∧ f i → f (vstd.math.sub i n)) → ∀ (i : Int), f i :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_induction_forall2 (n : Int) (f : Int → Int → Bool) :
    n > 0 →
      (∀ (i : Int) (j : Int), (0 ≤ i ∧ i < n) ∧ 0 ≤ j ∧ j < n → f i j) →
        (∀ (i : Int) (j : Int), i ≥ 0 ∧ f i j → f (vstd.math.add i n) j) →
          (∀ (i : Int) (j : Int), j ≥ 0 ∧ f i j → f i (vstd.math.add j n)) →
            (∀ (i : Int) (j : Int), i < n ∧ f i j → f (vstd.math.sub i n) j) →
              (∀ (i : Int) (j : Int), j < n ∧ f i j → f i (vstd.math.sub j n)) → ∀ (i : Int) (j : Int), f i j :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_auto_plus (n : Int) :
    n > 0 → vstd.arithmetic.internals.div_internals.div_auto_plus n :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_auto_minus (n : Int) :
    n > 0 → vstd.arithmetic.internals.div_internals.div_auto_minus n :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_auto (n : Int) :
    n > 0 → vstd.arithmetic.internals.div_internals.div_auto n :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_induction_auto (n : Int) (x : Int) (f : Int → Bool) :
    n > 0 →
      (vstd.arithmetic.internals.div_internals.div_auto n →
          ((∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ i < n → f i) ∧
              ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + n)) ∧
            ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le (i + 1) n ∧ f i → f (i - n)) →
        vstd.arithmetic.internals.div_internals.div_auto n ∧ f x :=
  sorry
theorem vstd.arithmetic.internals.div_internals.lemma_div_induction_auto_forall (n : Int) (f : Int → Bool) :
    n > 0 →
      (vstd.arithmetic.internals.div_internals.div_auto n →
          ((∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ i < n → f i) ∧
              ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + n)) ∧
            ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le (i + 1) n ∧ f i → f (i - n)) →
        vstd.arithmetic.internals.div_internals.div_auto n ∧ ∀ (i : Int), f i :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_induction_auto (n : Int) (x : Int) (f : Int → Bool) :
    n > 0 →
      (vstd.arithmetic.internals.mod_internals.mod_auto n →
          ((∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ i < n → f i) ∧
              ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + n)) ∧
            ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le (i + 1) n ∧ f i → f (i - n)) →
        vstd.arithmetic.internals.mod_internals.mod_auto n ∧ f x :=
  sorry
theorem vstd.arithmetic.internals.mod_internals.lemma_mod_induction_auto_forall (n : Int) (f : Int → Bool) :
    n > 0 →
      (vstd.arithmetic.internals.mod_internals.mod_auto n →
          ((∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ i < n → f i) ∧
              ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + n)) ∧
            ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le (i + 1) n ∧ f i → f (i - n)) →
        vstd.arithmetic.internals.mod_internals.mod_auto n ∧ ∀ (i : Int), f i :=
  sorry
theorem vstd.arithmetic.internals.mul_internals.lemma_mul_properties_internal_prove_mul_auto («no%param» : Int) :
    vstd.arithmetic.internals.mul_internals.mul_auto 0 :=
  sorry
theorem vstd.arithmetic.internals.mul_internals.lemma_mul_induction_auto_forall (f : Int → Bool) :
    (vstd.arithmetic.internals.mul_internals.mul_auto 0 →
        (f 0 ∧ ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le 0 i ∧ f i → f (i + 1)) ∧
          ∀ (i : Int), vstd.arithmetic.internals.general_internals.is_le i 0 ∧ f i → f (i - 1)) →
      vstd.arithmetic.internals.mul_internals.mul_auto 0 ∧ ∀ (i : Int), f i :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_is_div_recursive (x : Int) (d : Int) :
    0 < d → vstd.arithmetic.internals.div_internals.div_recursive x d = x / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_by_self (d : Int) : !d = 0 → d / d = 1 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_of0 (d : Int) : !d = 0 → 0 / d = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics (x : Int) :
    (!x = 0 → 0 / x = 0) ∧ x / 1 = x ∧ (!x = 0 → x / x = 1) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_1 (x : Int) : !x = 0 → 0 / x = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_2 (x : Int) : x / 1 = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_3 (x : Int) : !x = 0 → x / x = 1 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_4 (x : Int) (y : Int) : x ≥ 0 ∧ y > 0 → x / y ≥ 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_pos_is_pos (x : Int) (d : Int) : 0 ≤ x → 0 < d → 0 ≤ x / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_is_ordered (x : Int) (y : Int) (z : Int) : x ≤ y → 0 < z → x / z ≤ y / z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_is_ordered_by_denominator (x : Int) (y : Int) (z : Int) :
    0 ≤ x → 1 ≤ y ∧ y ≤ z → x / y ≥ x / z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_5 (x : Int) (y : Int) : x ≥ 0 ∧ y > 0 → x / y ≤ x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_basics_prove_auto («no%param» : Int) :
    (∀ (x : Int), !x = 0 → 0 / x = 0) ∧
      (∀ (x : Int), x / 1 = x) ∧
        (∀ (x : Int) (y : Int), x ≥ 0 ∧ y > 0 → x / y ≥ 0) ∧ ∀ (x : Int) (y : Int), x ≥ 0 ∧ y > 0 → x / y ≤ x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_small_div_converse (x : Int) (d : Int) : (0 ≤ x ∧ 0 < d) ∧ x / d = 0 → x < d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_non_zero (x : Int) (d : Int) : x ≥ d ∧ d > 0 → x / d > 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_is_strictly_smaller (x : Int) (d : Int) : 0 < x → 1 < d → x / d < x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_dividing_sums (a : Int) (b : Int) (d : Int) (r : Int) :
    0 < d → r = a % d + b % d - (a + b) % d → d * ((a + b) / d) - r = d * (a / d) + d * (b / d) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_plus_one (x : Int) (d : Int) : 0 < d → 1 + x / d = (d + x) / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_minus_one (x : Int) (d : Int) : 0 < d → 0 - 1 + x / d = (0 - d + x) / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_basic_div_specific_divisor (d : Int) :
    0 < d → ∀ (x : Int), 0 ≤ x ∧ x < d → x / d = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_basic_div : ∀ (x : Int) (d : Int), 0 ≤ x ∧ x < d → x / d = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_decreases (x : Int) (d : Int) : 0 < x → 1 < d → x / d < x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_nonincreasing (x : Int) (d : Int) : 0 ≤ x → 0 < d → x / d ≤ x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_small_mod (x : Nat) (m : Nat) : x < m → 0 < m → Int.natAbs (x % m) = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_is_distributive_auto («no%param» : Int) :
    (∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z) ∧
      (∀ (x : Int) (y : Int) (z : Int), (y + z) * x = y * x + z * x) ∧
        (∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z) ∧
          ∀ (x : Int) (y : Int) (z : Int), (y - z) * x = y * x - z * x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_is_commutative_auto («no%param» : Int) :
    ∀ (x : Int) (y : Int), x * y = y * x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_basics_1 (x : Int) : 0 * x = 0 :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_basics_2 (x : Int) : x * 0 = 0 :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_basics_3 (x : Int) : x * 1 = x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_basics_4 (x : Int) : 1 * x = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_basics_auto («no%param» : Int) :
    (∀ (x : Int), 0 * x = 0) ∧ (∀ (x : Int), x * 0 = 0) ∧ (∀ (x : Int), x * 1 = x) ∧ ∀ (x : Int), 1 * x = x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_strictly_positive (x : Int) (y : Int) : 0 < x ∧ 0 < y → 0 < x * y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_associative (x : Int) (y : Int) (z : Int) : x * (y * z) = x * y * z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_is_associative_auto («no%param» : Int) :
    ∀ (x : Int) (y : Int) (z : Int), x * (y * z) = x * y * z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_part_bound1 (a : Int) (b : Int) (c : Int) :
    0 ≤ a → 0 < b → 0 < c → 0 < b * c ∧ b * (a / b) % (b * c) ≤ b * (c - 1) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_self_0 (m : Int) : m > 0 → m % m = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_twice (x : Int) (m : Int) : m > 0 → x % m % m = x % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_division_less_than_divisor (x : Int) (m : Int) :
    m > 0 →
      let «tmp%%» := x % m;
      0 ≤ «tmp%%» ∧ «tmp%%» < m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_properties_auto («no%param» : Int) :
    (∀ (m : Int), m > 0 → m % m = 0) ∧
      (∀ (x : Int) (m : Int), m > 0 → x % m % m = x % m) ∧
        ∀ (x : Int) (m : Int),
          m > 0 →
            let «tmp%%» := x % m;
            0 ≤ «tmp%%» ∧ «tmp%%» < m :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_increases (x : Int) (y : Int) : 0 < x → 0 < y → y ≤ x * y :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_part_bound2 (x : Int) (y : Int) (z : Int) :
    0 ≤ x → 0 < y → 0 < z → y * z > 0 ∧ x % y % (y * z) < y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_nonnegative (x : Int) (y : Int) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_adds (a : Int) (b : Int) (d : Int) :
    0 < d →
      a % d + b % d = (a + b) % d + d * ((a % d + b % d) / d) ∧ (a % d + b % d < d → a % d + b % d = (a + b) % d) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse_helper_1 (u : Int) (d : Int) (r : Int) :
    !d = 0 → 0 ≤ r ∧ r < d → u = (u * d + r) / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_add_multiples_vanish (b : Int) (m : Int) : 0 < m → (m + b) % m = b % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse_helper_2 (u : Int) (d : Int) (r : Int) :
    !d = 0 → 0 ≤ r ∧ r < d → r = (u * d + r) % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse_mod (x : Int) (d : Int) (q : Int) (r : Int) :
    !d = 0 → 0 ≤ r ∧ r < d → x = q * d + r → r = x % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse_div (x : Int) (d : Int) (q : Int) (r : Int) :
    !d = 0 → 0 ≤ r ∧ r < d → x = q * d + r → q = x / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse (x : Int) (d : Int) (q : Int) (r : Int) :
    !d = 0 → 0 ≤ r ∧ r < d → x = q * d + r → r = x % d ∧ q = x / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod (x : Int) (d : Int) : !d = 0 → x = d * (x / d) + x % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_multiples_vanish (a : Int) (b : Int) (m : Int) :
    0 < m → (m * a + b) % m = b % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_hoist_over_denominator (x : Int) (j : Int) (d : Nat) :
    0 < d → x / d + j = (x + j * d) / d :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_unary_negation (x : Int) (y : Int) :
    let «tmp%%» := 0 - x * y;
    (0 - x) * y = «tmp%%» ∧ «tmp%%» = x * (0 - y) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_mod (x : Int) (a : Int) (b : Int) :
    0 < a → 0 < b → 0 < a * b ∧ x % (a * b) % a = x % a :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_add_mod_noop (x : Int) (y : Int) (m : Int) :
    0 < m → (x % m + y % m) % m = (x + y) % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_basics_auto («no%param» : Int) :
    (∀ (m : Int), m > 0 → m % m = 0) ∧ ∀ (x : Int) (m : Int), m > 0 → x % m % m = x % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_sub_mod_noop (x : Int) (y : Int) (m : Int) :
    0 < m → (x % m - y % m) % m = (x - y) % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_is_mod_recursive (x : Int) (m : Int) :
    m > 0 → vstd.arithmetic.internals.mod_internals.mod_recursive x m = x % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_is_mod_recursive_auto («no%param» : Int) :
    ∀ (x : Int) (d : Int), d > 0 → vstd.arithmetic.internals.mod_internals.mod_recursive x d = x % d :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_equality_converse (m : Int) (x : Int) (y : Int) :
    !m = 0 → m * x = m * y → x = y :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_denominator (x : Int) (c : Int) (d : Int) :
    0 ≤ x → 0 < c → 0 < d → !c * d = 0 ∧ x / c / d = x / (c * d) :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_basics (x : Int) : 0 * x = 0 ∧ x * 0 = 0 ∧ x * 1 = x ∧ 1 * x = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_multiples_vanish_fancy (x : Int) (b : Int) (d : Int) :
    0 < d → 0 ≤ b ∧ b < d → (d * x + b) / d = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_multiples_vanish (x : Int) (d : Int) : 0 < d → d * x / d = x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_by_multiple (b : Int) (d : Int) : 0 ≤ b → 0 < d → b * d / d = b :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_truncate_middle (x : Int) (b : Int) (c : Int) :
    0 ≤ x → 0 < b → 0 < c → 0 < b * c ∧ b * x % (b * c) = b * (x % c) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_breakdown (x : Int) (y : Int) (z : Int) :
    0 ≤ x → 0 < y → 0 < z → 0 < y * z ∧ x % (y * z) = y * (x / y % z) + x % y :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_remainder_upper (x : Int) (d : Int) : 0 ≤ x → 0 < d → x - d < x / d * d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_remainder_lower (x : Int) (d : Int) : 0 ≤ x → 0 < d → x ≥ x / d * d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_remainder (x : Int) (d : Int) :
    0 ≤ x →
      0 < d →
        let «tmp%%» := x - x / d * d;
        0 ≤ «tmp%%» ∧ «tmp%%» < d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_hoist_inequality (x : Int) (y : Int) (z : Int) :
    0 ≤ x → 0 < z → x * (y / z) ≤ x * y / z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_indistinguishable_quotients (a : Int) (b : Int) (d : Int) :
    0 < d →
      (let «tmp%%» := a - a % d;
        (0 ≤ «tmp%%» ∧ «tmp%%» ≤ b) ∧ b < a + d - a % d) →
        a / d = b / d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_multiples_vanish_quotient (x : Int) (a : Int) (d : Int) :
    0 < x → 0 ≤ a → 0 < d → 0 < x * d ∧ a / d = x * a / (x * d) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_round_down (a : Int) (r : Int) (d : Int) :
    0 < d → a % d = 0 → 0 ≤ r ∧ r < d → a = d * ((a + r) / d) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_multiples_basic (x : Int) (m : Int) : m > 0 → x * m % m = 0 :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_div_by_multiple_is_strongly_ordered (x : Int) (y : Int) (m : Int) (z : Int) :
    x < y → y = m * z → 0 < z → x / z < y / z :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_multiply_divide_le (a : Int) (b : Int) (c : Int) :
    0 < b → a ≤ b * c → a / b ≤ c :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_multiply_divide_lt (a : Int) (b : Int) (c : Int) :
    0 < b → a < b * c → a / b < c :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_decreases (x : Nat) (m : Nat) : 0 < m → Int.natAbs (x % m) ≤ x :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_is_zero (x : Nat) (m : Nat) :
    x > 0 ∧ m > 0 → Int.natAbs (x % m) = 0 → x ≥ m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_sub_multiples_vanish (b : Int) (m : Int) :
    0 < m → (0 - m + b) % m = b % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_subtraction (x : Nat) (s : Nat) (d : Nat) :
    0 < d → 0 ≤ s ∧ s ≤ Int.natAbs (x % d) → Int.natAbs (x % d) - Int.natAbs (s % d) = (x - s) % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_add_mod_noop_right (x : Int) (y : Int) (m : Int) :
    0 < m → (x + y % m) % m = (x + y) % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_sub_mod_noop_right (x : Int) (y : Int) (m : Int) :
    0 < m → (x - y % m) % m = (x - y) % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_neg_neg (x : Int) (d : Int) : 0 < d → x % d = x * (1 - d) % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_fundamental_div_mod_converse_prove_auto («no%param» : Int) :
    (∀ (x : Int) (d : Int) (q : Int) (r : Int), (!d = 0 ∧ 0 ≤ r ∧ r < d) ∧ x = q * d + r → q = x / d) ∧
      ∀ (x : Int) (d : Int) (q : Int) (r : Int), (!d = 0 ∧ 0 ≤ r ∧ r < d) ∧ x = q * d + r → r = x % d :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_pos_bound (x : Int) (m : Int) :
    0 ≤ x →
      0 < m →
        let «tmp%%» := x % m;
        0 ≤ «tmp%%» ∧ «tmp%%» < m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_bound (x : Int) (m : Int) :
    0 < m →
      let «tmp%%» := x % m;
      0 ≤ «tmp%%» ∧ «tmp%%» < m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_mod_noop_left (x : Int) (y : Int) (m : Int) :
    0 < m → x % m * y % m = x * y % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_mod_noop_right (x : Int) (y : Int) (m : Int) :
    0 < m → x * (y % m) % m = x * y % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_mod_noop_general (x : Int) (y : Int) (m : Int) :
    0 < m → x % m * y % m = x * y % m ∧ x * (y % m) % m = x * y % m ∧ x % m * (y % m) % m = x * y % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_mod_noop (x : Int) (y : Int) (m : Int) :
    0 < m → x % m * (y % m) % m = x * y % m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_equivalence (x : Int) (y : Int) (m : Int) :
    0 < m → (x % m = y % m) = ((x - y) % m = 0) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_mul_equivalent (x : Int) (y : Int) (z : Int) (m : Int) :
    m > 0 →
      vstd.arithmetic.div_mod.is_mod_equivalent x y m → vstd.arithmetic.div_mod.is_mod_equivalent (x * z) (y * z) m :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mul_is_distributive_sub_auto («no%param» : Int) :
    ∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_strictly_increases (x : Int) (y : Int) : 1 < x → 0 < y → y < x * y :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_ordering (x : Int) (k : Int) (d : Int) :
    1 < d → 0 < k → 0 < d * k ∧ x % d ≤ x % (d * k) :=
  sorry
theorem vstd.arithmetic.div_mod.lemma_mod_breakdown (x : Int) (y : Int) (z : Int) :
    0 ≤ x → 0 < y → 0 < z → y * z > 0 ∧ x % (y * z) = y * (x / y % z) + x % y :=
  sorry
theorem vstd.arithmetic.logarithm.lemma_log0 (base : Int) (pow : Int) :
    base > 1 → 0 ≤ pow ∧ pow < base → vstd.arithmetic.logarithm.log base pow = 0 :=
  sorry
theorem vstd.arithmetic.logarithm.lemma_log_s (base : Int) (pow : Int) :
    base > 1 →
      pow ≥ base →
        pow / base ≥ 0 ∧
          vstd.arithmetic.logarithm.log base pow = 1 + vstd.arithmetic.logarithm.log base (pow / base) :=
  sorry
theorem vstd.arithmetic.logarithm.lemma_log_nonnegative (base : Int) (pow : Int) :
    base > 1 → 0 ≤ pow → vstd.arithmetic.logarithm.log base pow ≥ 0 :=
  sorry
theorem vstd.arithmetic.logarithm.lemma_log_is_ordered (base : Int) (pow1 : Int) (pow2 : Int) :
    base > 1 →
      0 ≤ pow1 ∧ pow1 ≤ pow2 → vstd.arithmetic.logarithm.log base pow1 ≤ vstd.arithmetic.logarithm.log base pow2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow0 (b : Int) : vstd.arithmetic.power.pow b 0 = 1 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_positive (b : Int) (e : Nat) : b > 0 → 0 < vstd.arithmetic.power.pow b e :=
  sorry
theorem vstd.arithmetic.logarithm.lemma_log_pow (base : Int) (n : Nat) :
    base > 1 → vstd.arithmetic.logarithm.log base (vstd.arithmetic.power.pow base n) = n :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_mul_pos (x : Int) (y : Int) :
    x ≥ 0 → x * y = vstd.arithmetic.internals.mul_internals.mul_pos x y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_mul_recursive (x : Int) (y : Int) :
    x * y = vstd.arithmetic.internals.mul_internals.mul_recursive x y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_nonzero (x : Int) (y : Int) : (!x * y = 0) = (!x = 0 ∧ !y = 0) :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_by_zero_is_zero (x : Int) : x * 0 = 0 ∧ 0 * x = 0 :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_ordering (x : Int) (y : Int) :
    !x = 0 → !y = 0 → 0 ≤ x * y → x * y ≥ x ∧ x * y ≥ y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_strict_inequality (x : Int) (y : Int) (z : Int) :
    x < y → z > 0 → x * z < y * z :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_upper_bound (x : Int) (xbound : Int) (y : Int) (ybound : Int) :
    x ≤ xbound → y ≤ ybound → 0 ≤ x → 0 ≤ y → x * y ≤ xbound * ybound :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_strict_upper_bound (x : Int) (xbound : Int) (y : Int) (ybound : Int) :
    x < xbound → y < ybound → 0 < x → 0 < y → x * y ≤ (xbound - 1) * (ybound - 1) :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_left_inequality (x : Int) (y : Int) (z : Int) :
    0 < x → (y ≤ z → x * y ≤ x * z) ∧ (y < z → x * y < x * z) :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_inequality_converse (x : Int) (y : Int) (z : Int) :
    x * z ≤ y * z → z > 0 → x ≤ y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_strict_inequality_converse (x : Int) (y : Int) (z : Int) :
    x * z < y * z → z ≥ 0 → x < y :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_is_distributive (x : Int) (y : Int) (z : Int) :
    x * (y + z) = x * y + x * z ∧
      x * (y - z) = x * y - x * z ∧
        (y + z) * x = y * x + z * x ∧
          (y - z) * x = y * x - z * x ∧
            x * (y + z) = (y + z) * x ∧ x * (y - z) = (y - z) * x ∧ x * y = y * x ∧ x * z = z * x :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_cancels_negatives (x : Int) (y : Int) : x * y = (0 - x) * (0 - y) :=
  sorry
theorem vstd.arithmetic.mul.lemma_mul_properties_prove_mul_properties_auto («no%param» : Int) :
    (∀ (x : Int) (y : Int), x * y = y * x) ∧
      (∀ (x : Int),
          let «tmp%%» := 1 * x;
          x * 1 = «tmp%%» ∧ «tmp%%» = x) ∧
        (∀ (x : Int) (y : Int) (z : Int), x < y ∧ z > 0 → x * z < y * z) ∧
          (∀ (x : Int) (y : Int) (z : Int), x ≤ y ∧ z ≥ 0 → x * z ≤ y * z) ∧
            (∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z) ∧
              (∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z) ∧
                (∀ (x : Int) (y : Int) (z : Int), (y + z) * x = y * x + z * x) ∧
                  (∀ (x : Int) (y : Int) (z : Int), (y - z) * x = y * x - z * x) ∧
                    (∀ (x : Int) (y : Int) (z : Int), x * (y * z) = x * y * z) ∧
                      (∀ (x : Int) (y : Int), (!x * y = 0) = (!x = 0 ∧ !y = 0)) ∧
                        (∀ (x : Int) (y : Int), 0 ≤ x ∧ 0 ≤ y → 0 ≤ x * y) ∧
                          (∀ (x : Int) (y : Int), (0 < x ∧ 0 < y) ∧ 0 ≤ x * y → x ≤ x * y ∧ y ≤ x * y) ∧
                            (∀ (x : Int) (y : Int), 1 < x ∧ 0 < y → y < x * y) ∧
                              (∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → y ≤ x * y) ∧
                                ∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → 0 < x * y :=
  sorry
theorem vstd.arithmetic.power.lemma_mul_basics_auto («no%param» : Int) :
    (∀ (x : Int), 0 * x = 0) ∧ (∀ (x : Int), x * 0 = 0) ∧ (∀ (x : Int), x * 1 = x) ∧ ∀ (x : Int), 1 * x = x :=
  sorry
theorem vstd.arithmetic.power.lemma_pow1 (b : Int) : vstd.arithmetic.power.pow b 1 = b :=
  sorry
theorem vstd.arithmetic.power.lemma0_pow (e : Nat) : e > 0 → vstd.arithmetic.power.pow 0 e = 0 :=
  sorry
theorem vstd.arithmetic.power.lemma1_pow (e : Nat) : vstd.arithmetic.power.pow 1 e = 1 :=
  sorry
theorem vstd.arithmetic.power.lemma_square_is_pow2 (x : Int) : vstd.arithmetic.power.pow x 2 = x * x :=
  sorry
theorem vstd.arithmetic.power.lemma_mul_is_associative_auto («no%param» : Int) :
    ∀ (x : Int) (y : Int) (z : Int), x * (y * z) = x * y * z :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_adds (b : Int) (e1 : Nat) (e2 : Nat) :
    vstd.arithmetic.power.pow b (Int.natAbs (e1 + e2)) =
      vstd.arithmetic.power.pow b e1 * vstd.arithmetic.power.pow b e2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_sub_add_cancel (b : Int) (e1 : Nat) (e2 : Nat) :
    e1 ≥ e2 →
      vstd.arithmetic.power.pow b (Int.natAbs (e1 - e2)) * vstd.arithmetic.power.pow b e2 =
        vstd.arithmetic.power.pow b e1 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_subtracts (b : Int) (e1 : Nat) (e2 : Nat) :
    b > 0 →
      e1 ≤ e2 →
        vstd.arithmetic.power.pow b e1 > 0 ∧
          let «tmp%%» := vstd.arithmetic.power.pow b e2 / vstd.arithmetic.power.pow b e1;
          vstd.arithmetic.power.pow b (Int.natAbs (e2 - e1)) = «tmp%%» ∧ «tmp%%» > 0 :=
  sorry
theorem vstd.arithmetic.power.lemma_mul_is_distributive_auto («no%param» : Int) :
    (∀ (x : Int) (y : Int) (z : Int), x * (y + z) = x * y + x * z) ∧
      (∀ (x : Int) (y : Int) (z : Int), (y + z) * x = y * x + z * x) ∧
        (∀ (x : Int) (y : Int) (z : Int), x * (y - z) = x * y - x * z) ∧
          ∀ (x : Int) (y : Int) (z : Int), (y - z) * x = y * x - z * x :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_multiplies (a : Int) (b : Nat) (c : Nat) :
    0 ≤ Int.natAbs (b * c) ∧
      vstd.arithmetic.power.pow (vstd.arithmetic.power.pow a b) c =
        vstd.arithmetic.power.pow a (Int.natAbs (b * c)) :=
  sorry
theorem vstd.arithmetic.power.lemma_mul_is_commutative_auto («no%param» : Int) :
    ∀ (x : Int) (y : Int), x * y = y * x :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_distributes (a : Int) (b : Int) (e : Nat) :
    vstd.arithmetic.power.pow (a * b) e = vstd.arithmetic.power.pow a e * vstd.arithmetic.power.pow b e :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_properties_prove_pow_auto («no%param» : Int) :
    (∀ (x : Int), vstd.arithmetic.power.pow x 0 = 1) ∧
      (∀ (x : Int), vstd.arithmetic.power.pow x 1 = x) ∧
        (∀ (x : Int) (y : Int), y = 0 → vstd.arithmetic.power.pow x (Int.natAbs y) = 1) ∧
          (∀ (x : Int) (y : Int), y = 1 → vstd.arithmetic.power.pow x (Int.natAbs y) = x) ∧
            (∀ (x : Int) (y : Int), 0 < x ∧ 0 < y → x ≤ x * Int.natAbs y) ∧
              (∀ (x : Int) (y : Int), 0 < x ∧ 1 < y → x < x * Int.natAbs y) ∧
                (∀ (x : Int) (y : Nat) (z : Nat),
                    vstd.arithmetic.power.pow x (Int.natAbs (y + z)) =
                      vstd.arithmetic.power.pow x y * vstd.arithmetic.power.pow x z) ∧
                  (∀ (x : Int) (y : Nat) (z : Nat),
                      y ≥ z →
                        vstd.arithmetic.power.pow x (Int.natAbs (y - z)) * vstd.arithmetic.power.pow x z =
                          vstd.arithmetic.power.pow x y) ∧
                    ∀ (x : Int) (y : Nat) (z : Nat),
                      vstd.arithmetic.power.pow (x * y) z =
                        vstd.arithmetic.power.pow x z * vstd.arithmetic.power.pow y z :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_strictly_increases (b : Nat) (e1 : Nat) (e2 : Nat) :
    1 < b → e1 < e2 → vstd.arithmetic.power.pow b e1 < vstd.arithmetic.power.pow b e2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_increases (b : Nat) (e1 : Nat) (e2 : Nat) :
    b > 0 → e1 ≤ e2 → vstd.arithmetic.power.pow b e1 ≤ vstd.arithmetic.power.pow b e2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_strictly_increases_converse (b : Nat) (e1 : Nat) (e2 : Nat) :
    b > 0 → vstd.arithmetic.power.pow b e1 < vstd.arithmetic.power.pow b e2 → e1 < e2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_increases_converse (b : Nat) (e1 : Nat) (e2 : Nat) :
    1 < b → vstd.arithmetic.power.pow b e1 ≤ vstd.arithmetic.power.pow b e2 → e1 ≤ e2 :=
  sorry
theorem vstd.arithmetic.power.lemma_pull_out_pows (b : Nat) (x : Nat) (y : Nat) (z : Nat) :
    b > 0 →
      0 ≤ Int.natAbs (x * y) ∧
        0 ≤ Int.natAbs (y * z) ∧
          vstd.arithmetic.power.pow (vstd.arithmetic.power.pow b (Int.natAbs (x * y))) z =
            vstd.arithmetic.power.pow (vstd.arithmetic.power.pow b x) (Int.natAbs (y * z)) :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_division_inequality (x : Nat) (b : Nat) (e1 : Nat) (e2 : Nat) :
    b > 0 →
      e2 ≤ e1 →
        x < vstd.arithmetic.power.pow b e1 →
          vstd.arithmetic.power.pow b e2 > 0 ∧
            x / vstd.arithmetic.power.pow b e2 < vstd.arithmetic.power.pow b (Int.natAbs (e1 - e2)) :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_mod (b : Nat) (e : Nat) :
    b > 0 → e > 0 → vstd.arithmetic.power.pow b e % b = 0 :=
  sorry
theorem vstd.arithmetic.power.lemma_pow_mod_noop (b : Int) (e : Nat) (m : Int) :
    m > 0 → vstd.arithmetic.power.pow (b % m) e % m = vstd.arithmetic.power.pow b e % m :=
  sorry
theorem vstd.arithmetic.power2.lemma_pow2_pos (e : Nat) : vstd.arithmetic.power2.pow2 e > 0 :=
  sorry
theorem vstd.arithmetic.power2.lemma_pow2 (e : Nat) : vstd.arithmetic.power2.pow2 e = vstd.arithmetic.power.pow 2 e :=
  sorry
theorem vstd.arithmetic.power2.lemma_pow2_unfold (e : Nat) :
    e > 0 → vstd.arithmetic.power2.pow2 e = Int.natAbs (2 * vstd.arithmetic.power2.pow2 (Int.natAbs (e - 1))) :=
  sorry
theorem vstd.arithmetic.power2.lemma_pow2_adds (e1 : Nat) (e2 : Nat) :
    vstd.arithmetic.power2.pow2 (Int.natAbs (e1 + e2)) =
      Int.natAbs (vstd.arithmetic.power2.pow2 e1 * vstd.arithmetic.power2.pow2 e2) :=
  sorry
theorem vstd.arithmetic.power2.lemma_pow2_strictly_increases (e1 : Nat) (e2 : Nat) :
    e1 < e2 → vstd.arithmetic.power2.pow2 e1 < vstd.arithmetic.power2.pow2 e2 :=
  sorry
theorem vstd.arithmetic.power2.lemma2_to64 («no%param» : Int) :
    vstd.arithmetic.power2.pow2 0 = 1 ∧
      vstd.arithmetic.power2.pow2 1 = 2 ∧
        vstd.arithmetic.power2.pow2 2 = 4 ∧
          vstd.arithmetic.power2.pow2 3 = 8 ∧
            vstd.arithmetic.power2.pow2 4 = 16 ∧
              vstd.arithmetic.power2.pow2 5 = 32 ∧
                vstd.arithmetic.power2.pow2 6 = 64 ∧
                  vstd.arithmetic.power2.pow2 7 = 128 ∧
                    vstd.arithmetic.power2.pow2 8 = 256 ∧
                      vstd.arithmetic.power2.pow2 9 = 512 ∧
                        vstd.arithmetic.power2.pow2 10 = 1024 ∧
                          vstd.arithmetic.power2.pow2 11 = 2048 ∧
                            vstd.arithmetic.power2.pow2 12 = 4096 ∧
                              vstd.arithmetic.power2.pow2 13 = 8192 ∧
                                vstd.arithmetic.power2.pow2 14 = 16384 ∧
                                  vstd.arithmetic.power2.pow2 15 = 32768 ∧
                                    vstd.arithmetic.power2.pow2 16 = 65536 ∧
                                      vstd.arithmetic.power2.pow2 17 = 131072 ∧
                                        vstd.arithmetic.power2.pow2 18 = 262144 ∧
                                          vstd.arithmetic.power2.pow2 19 = 524288 ∧
                                            vstd.arithmetic.power2.pow2 20 = 1048576 ∧
                                              vstd.arithmetic.power2.pow2 21 = 2097152 ∧
                                                vstd.arithmetic.power2.pow2 22 = 4194304 ∧
                                                  vstd.arithmetic.power2.pow2 23 = 8388608 ∧
                                                    vstd.arithmetic.power2.pow2 24 = 16777216 ∧
                                                      vstd.arithmetic.power2.pow2 25 = 33554432 ∧
                                                        vstd.arithmetic.power2.pow2 26 = 67108864 ∧
                                                          vstd.arithmetic.power2.pow2 27 = 134217728 ∧
                                                            vstd.arithmetic.power2.pow2 28 = 268435456 ∧
                                                              vstd.arithmetic.power2.pow2 29 = 536870912 ∧
                                                                vstd.arithmetic.power2.pow2 30 = 1073741824 ∧
                                                                  vstd.arithmetic.power2.pow2 31 = 2147483648 ∧
                                                                    vstd.arithmetic.power2.pow2 32 = 4294967296 ∧
                                                                      vstd.arithmetic.power2.pow2 64 =
                                                                        18446744073709551616 :=
  sorry
