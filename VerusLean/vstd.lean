import VerusLean.VerusBuiltins
noncomputable section
open Classical

@[verus_attr]
def arithmetic.internals.general_internals.is_le
      (x : Int) (y : Int)
  : Bool
  := (
(x ≤ y))

@[verus_attr]
def arithmetic.internals.mod_internals_nonlinear.modulus
      (x : Int) (y : Int)
  : Int
  := (
(x % y))

@[verus_attr]
def arithmetic.internals.div_internals.div_pos
      (x : Int) (d : Int)
  : Int
  := (if (d > 0) then (
(if (x < 0) then (
((0 - 1) + (arithmetic.internals.div_internals.div_pos (x + d) d))) else (if (x < d) then (
0) else (
(1 + (arithmetic.internals.div_internals.div_pos (x - d) d)))))) else undefined)
termination_by Int.natAbs ((if (x < 0) then (
(d - x)) else (
x)))
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
def arithmetic.internals.div_internals.div_recursive
      (x : Int) (d : Int)
  : Int
  := (
(if (d > 0) then (
(arithmetic.internals.div_internals.div_pos x d)) else (
((0 - 1) * (arithmetic.internals.div_internals.div_pos x ((0 - 1) * d))))))

@[verus_attr]
def arithmetic.internals.div_internals.div_auto_plus
      (n : Int)
  : Bool
  := (
(∀ (x : Int) (y : Int), (
let z := ((x % n) + (y % n))
((((0 ≤ z) ∧ (z < n)) ∧ (((x + y) / n) = ((x / n) + (y / n)))) ∨ (((n ≤ z) ∧ (z < (n + n))) ∧ (((x + y) / n) = (((x / n) + (y / n)) + 1)))))))

@[verus_attr]
def arithmetic.internals.div_internals.div_auto_minus
      (n : Int)
  : Bool
  := (
(∀ (x : Int) (y : Int), (
let z := ((x % n) - (y % n))
((((0 ≤ z) ∧ (z < n)) ∧ (((x - y) / n) = ((x / n) - (y / n)))) ∨ ((((0 - n) ≤ z) ∧ (z < 0)) ∧ (((x - y) / n) = (((x / n) - (y / n)) - 1)))))))

@[verus_attr]
def arithmetic.internals.mod_internals.mod_auto_plus
      (n : Int)
  : Bool
  := (
(∀ (x : Int) (y : Int), (
let z := ((x % n) + (y % n))
((((0 ≤ z) ∧ (z < n)) ∧ (((x + y) % n) = z)) ∨ (((n ≤ z) ∧ (z < (n + n))) ∧ (((x + y) % n) = (z - n)))))))

@[verus_attr]
def arithmetic.internals.mod_internals.mod_auto_minus
      (n : Int)
  : Bool
  := (
(∀ (x : Int) (y : Int), (
let z := ((x % n) - (y % n))
((((0 ≤ z) ∧ (z < n)) ∧ (((x - y) % n) = z)) ∨ ((((0 - n) ≤ z) ∧ (z < 0)) ∧ (((x - y) % n) = (z + n)))))))

@[verus_attr]
def arithmetic.internals.mod_internals.mod_auto
      (n : Int)
  : Bool
  := (
(((((((n % n) = 0) ∧ (((0 - n) % n) = 0)) ∧ (∀ (x : Int), (((x % n) % n) = (x % n)))) ∧ (∀ (x : Int), (((0 ≤ x) ∧ (x < n)) = ((x % n) = x)))) ∧ (arithmetic.internals.mod_internals.mod_auto_plus n)) ∧ (arithmetic.internals.mod_internals.mod_auto_minus n)))

@[verus_attr]
def arithmetic.internals.div_internals.div_auto
      (n : Int)
  : Bool
  := (
(((((arithmetic.internals.mod_internals.mod_auto n) ∧ (
let «tmp%%» := (0 - ((0 - n) / n))
(((n / n) = «tmp%%») ∧ («tmp%%» = 1)))) ∧ (∀ (x : Int), (((0 ≤ x) ∧ (x < n)) = ((x / n) = 0)))) ∧ (arithmetic.internals.div_internals.div_auto_plus n)) ∧ (arithmetic.internals.div_internals.div_auto_minus n)))

@[verus_attr]
def arithmetic.internals.mod_internals.mod_recursive
      (x : Int) (d : Int)
  : Int
  := (if (d > 0) then (
(if (x < 0) then (
(arithmetic.internals.mod_internals.mod_recursive (d + x) d)) else (if (x < d) then (
x) else (
(arithmetic.internals.mod_internals.mod_recursive (x - d) d))))) else undefined)
termination_by Int.natAbs ((if (x < 0) then (
(d - x)) else (
x)))
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
def arithmetic.internals.mul_internals.mul_pos
      (x : Int) (y : Int)
  : Int
  := (
(if (x ≤ 0) then (
0) else (
(y + (arithmetic.internals.mul_internals.mul_pos (x - 1) y)))))
termination_by Int.natAbs (x)
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
def arithmetic.internals.mul_internals.mul_recursive
      (x : Int) (y : Int)
  : Int
  := (
(if (x ≥ 0) then (
(arithmetic.internals.mul_internals.mul_pos x y)) else (
((0 - 1) * (arithmetic.internals.mul_internals.mul_pos ((0 - 1) * x) y)))))

@[verus_attr]
def arithmetic.internals.mul_internals.mul_auto
      («no%param» : Int)
  : Bool
  := (
(((∀ (x : Int) (y : Int), ((x * y) = (y * x))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((x + y) * z) = ((x * z) + (y * z))))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((x - y) * z) = ((x * z) - (y * z))))))

@[verus_attr]
def arithmetic.div_mod.is_mod_equivalent
      (x : Int) (y : Int) (m : Int)
  : Bool
  := (
(((x % m) = (y % m)) = (((x - y) % m) = 0)))

@[verus_attr]
def arithmetic.logarithm.log
      (base : Int) (pow : Int)
  : Int
  := (
(if (((pow < base) ∨ ((pow / base) ≥ pow)) ∨ ((pow / base) < 0)) then (
0) else (
(1 + (arithmetic.logarithm.log base (pow / base))))))
termination_by Int.natAbs (pow)
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
def arithmetic.power.pow
      (b : Int) (e : Nat)
  : Int
  := (
(if (e = 0) then (
1) else (
(b * (arithmetic.power.pow b (clip Nat (e - 1)))))))
termination_by Int.natAbs (e)
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
def arithmetic.power2.pow2
      (e : Nat)
  : Nat
  := (
(clip Nat (arithmetic.power.pow 2 e)))
termination_by Int.natAbs (e)
decreasing_by all_goals (decreasing_with verus_default_tac)

@[verus_attr]
theorem arithmetic.internals.div_internals_nonlinear.lemma_div_of0
      (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : ((0 / d) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals_nonlinear.lemma_div_by_self
      (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : ((d / d) = 1)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals_nonlinear.lemma_small_div
      («no%param» : Int)
  : (∀ (x : Int) (d : Int), ((((0 ≤ x) ∧ (x < d)) ∧ (d > 0)) → ((x / d) = 0)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.general_internals.lemma_induction_helper_pos
      (n : Int) (f : (Int → Bool)) (x : Int)
      (_0 : (x ≥ 0) := by verus_default_tac) (_1 : (n > 0) := by verus_default_tac) (_2 : (∀ (i : Int), (((0 ≤ i) ∧ (i < n)) → (f i))) := by verus_default_tac) (_3 : (∀ (i : Int), (((i ≥ 0) ∧ (f i)) → (f (math.add i n)))) := by verus_default_tac) (_4 : (∀ (i : Int), (((i < n) ∧ (f i)) → (f (math.sub i n)))) := by verus_default_tac)
  : (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.general_internals.lemma_induction_helper_neg
      (n : Int) (f : (Int → Bool)) (x : Int)
      (_0 : (x < 0) := by verus_default_tac) (_1 : (n > 0) := by verus_default_tac) (_2 : (∀ (i : Int), (((0 ≤ i) ∧ (i < n)) → (f i))) := by verus_default_tac) (_3 : (∀ (i : Int), (((i ≥ 0) ∧ (f i)) → (f (math.add i n)))) := by verus_default_tac) (_4 : (∀ (i : Int), (((i < n) ∧ (f i)) → (f (math.sub i n)))) := by verus_default_tac)
  : (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.general_internals.lemma_induction_helper
      (n : Int) (f : (Int → Bool)) (x : Int)
      (_0 : (n > 0) := by verus_default_tac) (_1 : (∀ (i : Int), (((0 ≤ i) ∧ (i < n)) → (f i))) := by verus_default_tac) (_2 : (∀ (i : Int), (((i ≥ 0) ∧ (f i)) → (f (math.add i n)))) := by verus_default_tac) (_3 : (∀ (i : Int), (((i < n) ∧ (f i)) → (f (math.sub i n)))) := by verus_default_tac)
  : (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals_nonlinear.lemma_mod_of_zero_is_zero
      (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((0 % m) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals_nonlinear.lemma_fundamental_div_mod
      (x : Int) (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : (x = ((d * (x / d)) + (x % d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals_nonlinear.lemma_0_mod_anything
      («no%param» : Int)
  : (∀ (m : Int), ((m > 0) → ((arithmetic.internals.mod_internals_nonlinear.modulus 0 m) = 0)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals_nonlinear.lemma_small_mod
      (x : Nat) (m : Nat)
      (_0 : (x < m) := by verus_default_tac) (_1 : (0 < m) := by verus_default_tac)
  : ((arithmetic.internals.mod_internals_nonlinear.modulus x m) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals_nonlinear.lemma_mod_range
      (x : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : (
let «tmp%%» := (arithmetic.internals.mod_internals_nonlinear.modulus x m)
((0 ≤ «tmp%%») ∧ («tmp%%» < m)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_strictly_positive
      (x : Int) (y : Int)
  : (((0 < x) ∧ (0 < y)) → (0 < (x * y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_nonzero
      (x : Int) (y : Int)
  : ((!((x * y) = 0)) = ((!(x = 0)) ∧ (!(y = 0))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_is_associative
      (x : Int) (y : Int) (z : Int)
  : ((x * (y * z)) = ((x * y) * z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_is_distributive_add
      (x : Int) (y : Int) (z : Int)
  : ((x * (y + z)) = ((x * y) + (x * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_ordering
      (x : Int) (y : Int)
      (_0 : (!(x = 0)) := by verus_default_tac) (_1 : (!(y = 0)) := by verus_default_tac) (_2 : (0 ≤ (x * y)) := by verus_default_tac)
  : (((x * y) ≥ x) ∧ ((x * y) ≥ y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals_nonlinear.lemma_mul_strict_inequality
      (x : Int) (y : Int) (z : Int)
      (_0 : (x < y) := by verus_default_tac) (_1 : (z > 0) := by verus_default_tac)
  : ((x * z) < (y * z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_commutative
      (x : Int) (y : Int)
  : ((x * y) = (y * x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_distributive_add
      (x : Int) (y : Int) (z : Int)
  : ((x * (y + z)) = ((x * y) + (x * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_commutes
      (x : Int) (y : Int)
  : ((x * y) = (y * x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_successor
      («no%param» : Int)
  : (∀ (x : Int) (y : Int), (((x + 1) * y) = ((x * y) + y))) ∧ (∀ (x : Int) (y : Int), (((x - 1) * y) = ((x * y) - y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_induction
      (f : (Int → Bool))
      (_0 : (f 0) := by verus_default_tac) (_1 : (∀ (i : Int), (((i ≥ 0) ∧ (f i)) → (f (math.add i 1)))) := by verus_default_tac) (_2 : (∀ (i : Int), (((i ≤ 0) ∧ (f i)) → (f (math.sub i 1)))) := by verus_default_tac)
  : (∀ (i : Int), (f i))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_distributes_plus
      (x : Int) (y : Int) (z : Int)
  : (((x + y) * z) = ((x * z) + (y * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_distributes_minus
      (x : Int) (y : Int) (z : Int)
  : (((x - y) * z) = ((x * z) - (y * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_distributive_add_other_way
      (x : Int) (y : Int) (z : Int)
  : (((y + z) * x) = ((y * x) + (z * x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_distributive_sub
      (x : Int) (y : Int) (z : Int)
  : ((x * (y - z)) = ((x * y) - (x * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_distributive_sub_other_way
      (x : Int) (y : Int) (z : Int)
  : (((y - z) * x) = ((y * x) - (z * x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_induction_auto
      (x : Int) (f : (Int → Bool))
      (_0 : ((arithmetic.internals.mul_internals.mul_auto 0) → (
(((f 0) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + 1))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le i 0) ∧ (f i)) → (f (i - 1))))))) := by verus_default_tac)
  : (arithmetic.internals.mul_internals.mul_auto 0) ∧ (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_inequality
      (x : Int) (y : Int) (z : Int)
      (_0 : (x ≤ y) := by verus_default_tac) (_1 : (z ≥ 0) := by verus_default_tac)
  : ((x * z) ≤ (y * z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_add_denominator
      (n : Int) (x : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((x + n) % n) = (x % n))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_sub_denominator
      (n : Int) (x : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((x - n) % n) = (x % n))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_div_add_denominator
      (n : Int) (x : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((x + n) / n) = ((x / n) + 1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_div_sub_denominator
      (n : Int) (x : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((x - n) / n) = ((x / n) - 1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_below_denominator
      (n : Int) (x : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((0 ≤ x) ∧ (x < n)) = ((x % n) = x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_basics
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (∀ (x : Int), (((x + n) % n) = (x % n))) ∧ (∀ (x : Int), (((x - n) % n) = (x % n))) ∧ (∀ (x : Int), (((x + n) / n) = ((x / n) + 1))) ∧ (∀ (x : Int), (((x - n) / n) = ((x / n) - 1))) ∧ (∀ (x : Int), (((0 ≤ x) ∧ (x < n)) = ((x % n) = x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_quotient_and_remainder
      (x : Int) (q : Int) (r : Int) (n : Int)
      (_0 : (n > 0) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < n)) := by verus_default_tac) (_2 : (x = ((q * n) + r)) := by verus_default_tac)
  : (q = (x / n)) ∧ (r = (x % n))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_auto
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (arithmetic.internals.mod_internals.mod_auto n)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_basics
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (((n / n) = 1) ∧ ((0 - ((0 - n) / n)) = 1)) ∧ (∀ (x : Int), (((0 ≤ x) ∧ (x < n)) = ((x / n) = 0))) ∧ (∀ (x : Int), (((x + n) / n) = ((x / n) + 1))) ∧ (∀ (x : Int), (((x - n) / n) = ((x / n) - 1)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_induction_forall
      (n : Int) (f : (Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : (∀ (i : Int), (((0 ≤ i) ∧ (i < n)) → (f i))) := by verus_default_tac) (_2 : (∀ (i : Int), (((i ≥ 0) ∧ (f i)) → (f (math.add i n)))) := by verus_default_tac) (_3 : (∀ (i : Int), (((i < n) ∧ (f i)) → (f (math.sub i n)))) := by verus_default_tac)
  : (∀ (i : Int), (f i))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_induction_forall2
      (n : Int) (f : (Int → Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : (∀ (i : Int) (j : Int), ((((0 ≤ i) ∧ (i < n)) ∧ ((0 ≤ j) ∧ (j < n))) → (f i j))) := by verus_default_tac) (_2 : (∀ (i : Int) (j : Int), (((i ≥ 0) ∧ (f i j)) → (f (math.add i n) j))) := by verus_default_tac) (_3 : (∀ (i : Int) (j : Int), (((j ≥ 0) ∧ (f i j)) → (f i (math.add j n)))) := by verus_default_tac) (_4 : (∀ (i : Int) (j : Int), (((i < n) ∧ (f i j)) → (f (math.sub i n) j))) := by verus_default_tac) (_5 : (∀ (i : Int) (j : Int), (((j < n) ∧ (f i j)) → (f i (math.sub j n)))) := by verus_default_tac)
  : (∀ (i : Int) (j : Int), (f i j))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_auto_plus
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (arithmetic.internals.div_internals.div_auto_plus n)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_auto_minus
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (arithmetic.internals.div_internals.div_auto_minus n)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_auto
      (n : Int)
      (_0 : (n > 0) := by verus_default_tac)
  : (arithmetic.internals.div_internals.div_auto n)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_induction_auto
      (n : Int) (x : Int) (f : (Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : ((arithmetic.internals.div_internals.div_auto n) → (
(((∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (i < n)) → (f i))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + n))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le (i + 1) n) ∧ (f i)) → (f (i - n))))))) := by verus_default_tac)
  : (arithmetic.internals.div_internals.div_auto n) ∧ (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.div_internals.lemma_div_induction_auto_forall
      (n : Int) (f : (Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : ((arithmetic.internals.div_internals.div_auto n) → (
(((∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (i < n)) → (f i))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + n))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le (i + 1) n) ∧ (f i)) → (f (i - n))))))) := by verus_default_tac)
  : (arithmetic.internals.div_internals.div_auto n) ∧ (∀ (i : Int), (f i))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_induction_auto
      (n : Int) (x : Int) (f : (Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : ((arithmetic.internals.mod_internals.mod_auto n) → (
(((∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (i < n)) → (f i))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + n))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le (i + 1) n) ∧ (f i)) → (f (i - n))))))) := by verus_default_tac)
  : (arithmetic.internals.mod_internals.mod_auto n) ∧ (f x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mod_internals.lemma_mod_induction_auto_forall
      (n : Int) (f : (Int → Bool))
      (_0 : (n > 0) := by verus_default_tac) (_1 : ((arithmetic.internals.mod_internals.mod_auto n) → (
(((∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (i < n)) → (f i))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + n))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le (i + 1) n) ∧ (f i)) → (f (i - n))))))) := by verus_default_tac)
  : (arithmetic.internals.mod_internals.mod_auto n) ∧ (∀ (i : Int), (f i))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_properties_internal_prove_mul_auto
      («no%param» : Int)
  : (arithmetic.internals.mul_internals.mul_auto 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.internals.mul_internals.lemma_mul_induction_auto_forall
      (f : (Int → Bool))
      (_0 : ((arithmetic.internals.mul_internals.mul_auto 0) → (
(((f 0) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le 0 i) ∧ (f i)) → (f (i + 1))))) ∧ (∀ (i : Int), (((arithmetic.internals.general_internals.is_le i 0) ∧ (f i)) → (f (i - 1))))))) := by verus_default_tac)
  : (arithmetic.internals.mul_internals.mul_auto 0) ∧ (∀ (i : Int), (f i))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_is_div_recursive
      (x : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : ((arithmetic.internals.div_internals.div_recursive x d) = (x / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_by_self
      (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : ((d / d) = 1)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_of0
      (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : ((0 / d) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics
      (x : Int)
  : ((!(x = 0)) → ((0 / x) = 0)) ∧ ((x / 1) = x) ∧ ((!(x = 0)) → ((x / x) = 1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_1
      (x : Int)
  : ((!(x = 0)) → ((0 / x) = 0))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_2
      (x : Int)
  : ((x / 1) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_3
      (x : Int)
  : ((!(x = 0)) → ((x / x) = 1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_4
      (x : Int) (y : Int)
  : (((x ≥ 0) ∧ (y > 0)) → ((x / y) ≥ 0))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_pos_is_pos
      (x : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : (0 ≤ (x / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_is_ordered
      (x : Int) (y : Int) (z : Int)
      (_0 : (x ≤ y) := by verus_default_tac) (_1 : (0 < z) := by verus_default_tac)
  : ((x / z) ≤ (y / z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_is_ordered_by_denominator
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : ((1 ≤ y) ∧ (y ≤ z)) := by verus_default_tac)
  : ((x / y) ≥ (x / z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_5
      (x : Int) (y : Int)
  : (((x ≥ 0) ∧ (y > 0)) → ((x / y) ≤ x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_basics_prove_auto
      («no%param» : Int)
  : (∀ (x : Int), ((!(x = 0)) → ((0 / x) = 0))) ∧ (∀ (x : Int), ((x / 1) = x)) ∧ (∀ (x : Int) (y : Int), (((x ≥ 0) ∧ (y > 0)) → ((x / y) ≥ 0))) ∧ (∀ (x : Int) (y : Int), (((x ≥ 0) ∧ (y > 0)) → ((x / y) ≤ x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_small_div_converse
      (x : Int) (d : Int)
  : ((((0 ≤ x) ∧ (0 < d)) ∧ ((x / d) = 0)) → (x < d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_non_zero
      (x : Int) (d : Int)
      (_0 : ((x ≥ d) ∧ (d > 0)) := by verus_default_tac)
  : ((x / d) > 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_is_strictly_smaller
      (x : Int) (d : Int)
      (_0 : (0 < x) := by verus_default_tac) (_1 : (1 < d) := by verus_default_tac)
  : ((x / d) < x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_dividing_sums
      (a : Int) (b : Int) (d : Int) (r : Int)
      (_0 : (0 < d) := by verus_default_tac) (_1 : (r = (((a % d) + (b % d)) - ((a + b) % d))) := by verus_default_tac)
  : (((d * ((a + b) / d)) - r) = ((d * (a / d)) + (d * (b / d))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_plus_one
      (x : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : ((1 + (x / d)) = ((d + x) / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_minus_one
      (x : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : (((0 - 1) + (x / d)) = (((0 - d) + x) / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_basic_div_specific_divisor
      (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : (∀ (x : Int), (((0 ≤ x) ∧ (x < d)) → ((x / d) = 0)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_basic_div
  : (∀ (x : Int) (d : Int), (((0 ≤ x) ∧ (x < d)) → ((x / d) = 0)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_decreases
      (x : Int) (d : Int)
      (_0 : (0 < x) := by verus_default_tac) (_1 : (1 < d) := by verus_default_tac)
  : ((x / d) < x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_nonincreasing
      (x : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : ((x / d) ≤ x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_small_mod
      (x : Nat) (m : Nat)
      (_0 : (x < m) := by verus_default_tac) (_1 : (0 < m) := by verus_default_tac)
  : ((clip Nat (x % m)) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_is_distributive_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int) (z : Int), ((x * (y + z)) = ((x * y) + (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y + z) * x) = ((y * x) + (z * x)))) ∧ (∀ (x : Int) (y : Int) (z : Int), ((x * (y - z)) = ((x * y) - (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y - z) * x) = ((y * x) - (z * x))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_is_commutative_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int), ((x * y) = (y * x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_basics_1
      (x : Int)
  : ((0 * x) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_basics_2
      (x : Int)
  : ((x * 0) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_basics_3
      (x : Int)
  : ((x * 1) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_basics_4
      (x : Int)
  : ((1 * x) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_basics_auto
      («no%param» : Int)
  : (∀ (x : Int), ((0 * x) = 0)) ∧ (∀ (x : Int), ((x * 0) = 0)) ∧ (∀ (x : Int), ((x * 1) = x)) ∧ (∀ (x : Int), ((1 * x) = x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_strictly_positive
      (x : Int) (y : Int)
  : (((0 < x) ∧ (0 < y)) → (0 < (x * y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_associative
      (x : Int) (y : Int) (z : Int)
  : ((x * (y * z)) = ((x * y) * z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_is_associative_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int) (z : Int), ((x * (y * z)) = ((x * y) * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_part_bound1
      (a : Int) (b : Int) (c : Int)
      (_0 : (0 ≤ a) := by verus_default_tac) (_1 : (0 < b) := by verus_default_tac) (_2 : (0 < c) := by verus_default_tac)
  : (0 < (b * c)) ∧ (((b * (a / b)) % (b * c)) ≤ (b * (c - 1)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_self_0
      (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : ((m % m) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_twice
      (x : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : (((x % m) % m) = (x % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_division_less_than_divisor
      (x : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : (
let «tmp%%» := (x % m)
((0 ≤ «tmp%%») ∧ («tmp%%» < m)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_properties_auto
      («no%param» : Int)
  : (∀ (m : Int), ((m > 0) → ((m % m) = 0))) ∧ (∀ (x : Int) (m : Int), ((m > 0) → (((x % m) % m) = (x % m)))) ∧ (∀ (x : Int) (m : Int), ((m > 0) → (
let «tmp%%» := (x % m)
((0 ≤ «tmp%%») ∧ («tmp%%» < m)))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_increases
      (x : Int) (y : Int)
      (_0 : (0 < x) := by verus_default_tac) (_1 : (0 < y) := by verus_default_tac)
  : (y ≤ (x * y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_part_bound2
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < y) := by verus_default_tac) (_2 : (0 < z) := by verus_default_tac)
  : ((y * z) > 0) ∧ (((x % y) % (y * z)) < y)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_nonnegative
      (x : Int) (y : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 ≤ y) := by verus_default_tac)
  : (0 ≤ (x * y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_adds
      (a : Int) (b : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : (((a % d) + (b % d)) = (((a + b) % d) + (d * (((a % d) + (b % d)) / d)))) ∧ ((((a % d) + (b % d)) < d) → (((a % d) + (b % d)) = ((a + b) % d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse_helper_1
      (u : Int) (d : Int) (r : Int)
      (_0 : (!(d = 0)) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac)
  : (u = (((u * d) + r) / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_add_multiples_vanish
      (b : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (((m + b) % m) = (b % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse_helper_2
      (u : Int) (d : Int) (r : Int)
      (_0 : (!(d = 0)) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac)
  : (r = (((u * d) + r) % d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse_mod
      (x : Int) (d : Int) (q : Int) (r : Int)
      (_0 : (!(d = 0)) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac) (_2 : (x = ((q * d) + r)) := by verus_default_tac)
  : (r = (x % d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse_div
      (x : Int) (d : Int) (q : Int) (r : Int)
      (_0 : (!(d = 0)) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac) (_2 : (x = ((q * d) + r)) := by verus_default_tac)
  : (q = (x / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse
      (x : Int) (d : Int) (q : Int) (r : Int)
      (_0 : (!(d = 0)) := by verus_default_tac) (_1 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac) (_2 : (x = ((q * d) + r)) := by verus_default_tac)
  : (r = (x % d)) ∧ (q = (x / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod
      (x : Int) (d : Int)
      (_0 : (!(d = 0)) := by verus_default_tac)
  : (x = ((d * (x / d)) + (x % d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_multiples_vanish
      (a : Int) (b : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((m * a) + b) % m) = (b % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_hoist_over_denominator
      (x : Int) (j : Int) (d : Nat)
      (_0 : (0 < d) := by verus_default_tac)
  : (((x / d) + j) = ((x + (j * d)) / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_unary_negation
      (x : Int) (y : Int)
  : (
let «tmp%%» := (0 - (x * y))
((((0 - x) * y) = «tmp%%») ∧ («tmp%%» = (x * (0 - y)))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_mod
      (x : Int) (a : Int) (b : Int)
      (_0 : (0 < a) := by verus_default_tac) (_1 : (0 < b) := by verus_default_tac)
  : (0 < (a * b)) ∧ (((x % (a * b)) % a) = (x % a))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_add_mod_noop
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((x % m) + (y % m)) % m) = ((x + y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_basics_auto
      («no%param» : Int)
  : (∀ (m : Int), ((m > 0) → ((m % m) = 0))) ∧ (∀ (x : Int) (m : Int), ((m > 0) → (((x % m) % m) = (x % m))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_sub_mod_noop
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((x % m) - (y % m)) % m) = ((x - y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_is_mod_recursive
      (x : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : ((arithmetic.internals.mod_internals.mod_recursive x m) = (x % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_is_mod_recursive_auto
      («no%param» : Int)
  : (∀ (x : Int) (d : Int), ((d > 0) → ((arithmetic.internals.mod_internals.mod_recursive x d) = (x % d))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_equality_converse
      (m : Int) (x : Int) (y : Int)
      (_0 : (!(m = 0)) := by verus_default_tac) (_1 : ((m * x) = (m * y)) := by verus_default_tac)
  : (x = y)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_denominator
      (x : Int) (c : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < c) := by verus_default_tac) (_2 : (0 < d) := by verus_default_tac)
  : (!((c * d) = 0)) ∧ (((x / c) / d) = (x / (c * d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_basics
      (x : Int)
  : ((0 * x) = 0) ∧ ((x * 0) = 0) ∧ ((x * 1) = x) ∧ ((1 * x) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_multiples_vanish_fancy
      (x : Int) (b : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac) (_1 : ((0 ≤ b) ∧ (b < d)) := by verus_default_tac)
  : ((((d * x) + b) / d) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_multiples_vanish
      (x : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : (((d * x) / d) = x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_by_multiple
      (b : Int) (d : Int)
      (_0 : (0 ≤ b) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : (((b * d) / d) = b)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_truncate_middle
      (x : Int) (b : Int) (c : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < b) := by verus_default_tac) (_2 : (0 < c) := by verus_default_tac)
  : (0 < (b * c)) ∧ (((b * x) % (b * c)) = (b * (x % c)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_breakdown
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < y) := by verus_default_tac) (_2 : (0 < z) := by verus_default_tac)
  : (0 < (y * z)) ∧ ((x % (y * z)) = ((y * ((x / y) % z)) + (x % y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_remainder_upper
      (x : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : ((x - d) < ((x / d) * d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_remainder_lower
      (x : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : (x ≥ ((x / d) * d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_remainder
      (x : Int) (d : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < d) := by verus_default_tac)
  : (
let «tmp%%» := (x - ((x / d) * d))
((0 ≤ «tmp%%») ∧ («tmp%%» < d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_hoist_inequality
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < z) := by verus_default_tac)
  : ((x * (y / z)) ≤ ((x * y) / z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_indistinguishable_quotients
      (a : Int) (b : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac) (_1 : (
let «tmp%%» := (a - (a % d))
(((0 ≤ «tmp%%») ∧ («tmp%%» ≤ b)) ∧ (b < ((a + d) - (a % d))))) := by verus_default_tac)
  : ((a / d) = (b / d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_multiples_vanish_quotient
      (x : Int) (a : Int) (d : Int)
      (_0 : (0 < x) := by verus_default_tac) (_1 : (0 ≤ a) := by verus_default_tac) (_2 : (0 < d) := by verus_default_tac)
  : (0 < (x * d)) ∧ ((a / d) = ((x * a) / (x * d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_round_down
      (a : Int) (r : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac) (_1 : ((a % d) = 0) := by verus_default_tac) (_2 : ((0 ≤ r) ∧ (r < d)) := by verus_default_tac)
  : (a = (d * ((a + r) / d)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_multiples_basic
      (x : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : (((x * m) % m) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_div_by_multiple_is_strongly_ordered
      (x : Int) (y : Int) (m : Int) (z : Int)
      (_0 : (x < y) := by verus_default_tac) (_1 : (y = (m * z)) := by verus_default_tac) (_2 : (0 < z) := by verus_default_tac)
  : ((x / z) < (y / z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_multiply_divide_le
      (a : Int) (b : Int) (c : Int)
      (_0 : (0 < b) := by verus_default_tac) (_1 : (a ≤ (b * c)) := by verus_default_tac)
  : ((a / b) ≤ c)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_multiply_divide_lt
      (a : Int) (b : Int) (c : Int)
      (_0 : (0 < b) := by verus_default_tac) (_1 : (a < (b * c)) := by verus_default_tac)
  : ((a / b) < c)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_decreases
      (x : Nat) (m : Nat)
      (_0 : (0 < m) := by verus_default_tac)
  : ((clip Nat (x % m)) ≤ x)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_is_zero
      (x : Nat) (m : Nat)
      (_0 : ((x > 0) ∧ (m > 0)) := by verus_default_tac) (_1 : ((clip Nat (x % m)) = 0) := by verus_default_tac)
  : (x ≥ m)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_sub_multiples_vanish
      (b : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((0 - m) + b) % m) = (b % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_subtraction
      (x : Nat) (s : Nat) (d : Nat)
      (_0 : (0 < d) := by verus_default_tac) (_1 : ((0 ≤ s) ∧ (s ≤ (clip Nat (x % d)))) := by verus_default_tac)
  : (((clip Nat (x % d)) - (clip Nat (s % d))) = ((x - s) % d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_add_mod_noop_right
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (((x + (y % m)) % m) = ((x + y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_sub_mod_noop_right
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (((x - (y % m)) % m) = ((x - y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_neg_neg
      (x : Int) (d : Int)
      (_0 : (0 < d) := by verus_default_tac)
  : ((x % d) = ((x * (1 - d)) % d))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_fundamental_div_mod_converse_prove_auto
      («no%param» : Int)
  : (∀ (x : Int) (d : Int) (q : Int) (r : Int), ((((!(d = 0)) ∧ ((0 ≤ r) ∧ (r < d))) ∧ (x = ((q * d) + r))) → (q = (x / d)))) ∧ (∀ (x : Int) (d : Int) (q : Int) (r : Int), ((((!(d = 0)) ∧ ((0 ≤ r) ∧ (r < d))) ∧ (x = ((q * d) + r))) → (r = (x % d))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_pos_bound
      (x : Int) (m : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < m) := by verus_default_tac)
  : (
let «tmp%%» := (x % m)
((0 ≤ «tmp%%») ∧ («tmp%%» < m)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_bound
      (x : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (
let «tmp%%» := (x % m)
((0 ≤ «tmp%%») ∧ («tmp%%» < m)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_mod_noop_left
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((x % m) * y) % m) = ((x * y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_mod_noop_right
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (((x * (y % m)) % m) = ((x * y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_mod_noop_general
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((x % m) * y) % m) = ((x * y) % m)) ∧ (((x * (y % m)) % m) = ((x * y) % m)) ∧ ((((x % m) * (y % m)) % m) = ((x * y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_mod_noop
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : ((((x % m) * (y % m)) % m) = ((x * y) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_equivalence
      (x : Int) (y : Int) (m : Int)
      (_0 : (0 < m) := by verus_default_tac)
  : (((x % m) = (y % m)) = (((x - y) % m) = 0))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_mul_equivalent
      (x : Int) (y : Int) (z : Int) (m : Int)
      (_0 : (m > 0) := by verus_default_tac) (_1 : (arithmetic.div_mod.is_mod_equivalent x y m) := by verus_default_tac)
  : (arithmetic.div_mod.is_mod_equivalent (x * z) (y * z) m)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mul_is_distributive_sub_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int) (z : Int), ((x * (y - z)) = ((x * y) - (x * z))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_strictly_increases
      (x : Int) (y : Int)
      (_0 : (1 < x) := by verus_default_tac) (_1 : (0 < y) := by verus_default_tac)
  : (y < (x * y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_ordering
      (x : Int) (k : Int) (d : Int)
      (_0 : (1 < d) := by verus_default_tac) (_1 : (0 < k) := by verus_default_tac)
  : (0 < (d * k)) ∧ ((x % d) ≤ (x % (d * k)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.div_mod.lemma_mod_breakdown
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 ≤ x) := by verus_default_tac) (_1 : (0 < y) := by verus_default_tac) (_2 : (0 < z) := by verus_default_tac)
  : ((y * z) > 0) ∧ ((x % (y * z)) = ((y * ((x / y) % z)) + (x % y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.logarithm.lemma_log0
      (base : Int) (pow : Int)
      (_0 : (base > 1) := by verus_default_tac) (_1 : ((0 ≤ pow) ∧ (pow < base)) := by verus_default_tac)
  : ((arithmetic.logarithm.log base pow) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.logarithm.lemma_log_s
      (base : Int) (pow : Int)
      (_0 : (base > 1) := by verus_default_tac) (_1 : (pow ≥ base) := by verus_default_tac)
  : ((pow / base) ≥ 0) ∧ ((arithmetic.logarithm.log base pow) = (1 + (arithmetic.logarithm.log base (pow / base))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.logarithm.lemma_log_nonnegative
      (base : Int) (pow : Int)
      (_0 : (base > 1) := by verus_default_tac) (_1 : (0 ≤ pow) := by verus_default_tac)
  : ((arithmetic.logarithm.log base pow) ≥ 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.logarithm.lemma_log_is_ordered
      (base : Int) (pow1 : Int) (pow2 : Int)
      (_0 : (base > 1) := by verus_default_tac) (_1 : ((0 ≤ pow1) ∧ (pow1 ≤ pow2)) := by verus_default_tac)
  : ((arithmetic.logarithm.log base pow1) ≤ (arithmetic.logarithm.log base pow2))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow0
      (b : Int)
  : ((arithmetic.power.pow b 0) = 1)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_positive
      (b : Int) (e : Nat)
      (_0 : (b > 0) := by verus_default_tac)
  : (0 < (arithmetic.power.pow b e))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.logarithm.lemma_log_pow
      (base : Int) (n : Nat)
      (_0 : (base > 1) := by verus_default_tac)
  : ((arithmetic.logarithm.log base (arithmetic.power.pow base n)) = n)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_mul_pos
      (x : Int) (y : Int)
      (_0 : (x ≥ 0) := by verus_default_tac)
  : ((x * y) = (arithmetic.internals.mul_internals.mul_pos x y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_mul_recursive
      (x : Int) (y : Int)
  : ((x * y) = (arithmetic.internals.mul_internals.mul_recursive x y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_nonzero
      (x : Int) (y : Int)
  : ((!((x * y) = 0)) = ((!(x = 0)) ∧ (!(y = 0))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_by_zero_is_zero
      (x : Int)
  : (((x * 0) = 0) ∧ ((0 * x) = 0))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_ordering
      (x : Int) (y : Int)
      (_0 : (!(x = 0)) := by verus_default_tac) (_1 : (!(y = 0)) := by verus_default_tac) (_2 : (0 ≤ (x * y)) := by verus_default_tac)
  : (((x * y) ≥ x) ∧ ((x * y) ≥ y))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_strict_inequality
      (x : Int) (y : Int) (z : Int)
      (_0 : (x < y) := by verus_default_tac) (_1 : (z > 0) := by verus_default_tac)
  : ((x * z) < (y * z))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_upper_bound
      (x : Int) (xbound : Int) (y : Int) (ybound : Int)
      (_0 : (x ≤ xbound) := by verus_default_tac) (_1 : (y ≤ ybound) := by verus_default_tac) (_2 : (0 ≤ x) := by verus_default_tac) (_3 : (0 ≤ y) := by verus_default_tac)
  : ((x * y) ≤ (xbound * ybound))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_strict_upper_bound
      (x : Int) (xbound : Int) (y : Int) (ybound : Int)
      (_0 : (x < xbound) := by verus_default_tac) (_1 : (y < ybound) := by verus_default_tac) (_2 : (0 < x) := by verus_default_tac) (_3 : (0 < y) := by verus_default_tac)
  : ((x * y) ≤ ((xbound - 1) * (ybound - 1)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_left_inequality
      (x : Int) (y : Int) (z : Int)
      (_0 : (0 < x) := by verus_default_tac)
  : ((y ≤ z) → ((x * y) ≤ (x * z))) ∧ ((y < z) → ((x * y) < (x * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_inequality_converse
      (x : Int) (y : Int) (z : Int)
      (_0 : ((x * z) ≤ (y * z)) := by verus_default_tac) (_1 : (z > 0) := by verus_default_tac)
  : (x ≤ y)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_strict_inequality_converse
      (x : Int) (y : Int) (z : Int)
      (_0 : ((x * z) < (y * z)) := by verus_default_tac) (_1 : (z ≥ 0) := by verus_default_tac)
  : (x < y)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_is_distributive
      (x : Int) (y : Int) (z : Int)
  : ((x * (y + z)) = ((x * y) + (x * z))) ∧ ((x * (y - z)) = ((x * y) - (x * z))) ∧ (((y + z) * x) = ((y * x) + (z * x))) ∧ (((y - z) * x) = ((y * x) - (z * x))) ∧ ((x * (y + z)) = ((y + z) * x)) ∧ ((x * (y - z)) = ((y - z) * x)) ∧ ((x * y) = (y * x)) ∧ ((x * z) = (z * x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_cancels_negatives
      (x : Int) (y : Int)
  : ((x * y) = ((0 - x) * (0 - y)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.mul.lemma_mul_properties_prove_mul_properties_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int), ((x * y) = (y * x))) ∧ (∀ (x : Int), (
let «tmp%%» := (1 * x)
(((x * 1) = «tmp%%») ∧ («tmp%%» = x)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((x < y) ∧ (z > 0)) → ((x * z) < (y * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((x ≤ y) ∧ (z ≥ 0)) → ((x * z) ≤ (y * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), ((x * (y + z)) = ((x * y) + (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), ((x * (y - z)) = ((x * y) - (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y + z) * x) = ((y * x) + (z * x)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y - z) * x) = ((y * x) - (z * x)))) ∧ (∀ (x : Int) (y : Int) (z : Int), ((x * (y * z)) = ((x * y) * z))) ∧ (∀ (x : Int) (y : Int), ((!((x * y) = 0)) = ((!(x = 0)) ∧ (!(y = 0))))) ∧ (∀ (x : Int) (y : Int), (((0 ≤ x) ∧ (0 ≤ y)) → (0 ≤ (x * y)))) ∧ (∀ (x : Int) (y : Int), ((((0 < x) ∧ (0 < y)) ∧ (0 ≤ (x * y))) → ((x ≤ (x * y)) ∧ (y ≤ (x * y))))) ∧ (∀ (x : Int) (y : Int), (((1 < x) ∧ (0 < y)) → (y < (x * y)))) ∧ (∀ (x : Int) (y : Int), (((0 < x) ∧ (0 < y)) → (y ≤ (x * y)))) ∧ (∀ (x : Int) (y : Int), (((0 < x) ∧ (0 < y)) → (0 < (x * y))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_mul_basics_auto
      («no%param» : Int)
  : (∀ (x : Int), ((0 * x) = 0)) ∧ (∀ (x : Int), ((x * 0) = 0)) ∧ (∀ (x : Int), ((x * 1) = x)) ∧ (∀ (x : Int), ((1 * x) = x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow1
      (b : Int)
  : ((arithmetic.power.pow b 1) = b)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma0_pow
      (e : Nat)
      (_0 : (e > 0) := by verus_default_tac)
  : ((arithmetic.power.pow 0 e) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma1_pow
      (e : Nat)
  : ((arithmetic.power.pow 1 e) = 1)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_square_is_pow2
      (x : Int)
  : ((arithmetic.power.pow x 2) = (x * x))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_mul_is_associative_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int) (z : Int), ((x * (y * z)) = ((x * y) * z)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_adds
      (b : Int) (e1 : Nat) (e2 : Nat)
  : ((arithmetic.power.pow b (clip Nat (e1 + e2))) = ((arithmetic.power.pow b e1) * (arithmetic.power.pow b e2)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_sub_add_cancel
      (b : Int) (e1 : Nat) (e2 : Nat)
      (_0 : (e1 ≥ e2) := by verus_default_tac)
  : (((arithmetic.power.pow b (clip Nat (e1 - e2))) * (arithmetic.power.pow b e2)) = (arithmetic.power.pow b e1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_subtracts
      (b : Int) (e1 : Nat) (e2 : Nat)
      (_0 : (b > 0) := by verus_default_tac) (_1 : (e1 ≤ e2) := by verus_default_tac)
  : ((arithmetic.power.pow b e1) > 0) ∧ (
let «tmp%%» := ((arithmetic.power.pow b e2) / (arithmetic.power.pow b e1))
(((arithmetic.power.pow b (clip Nat (e2 - e1))) = «tmp%%») ∧ («tmp%%» > 0)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_mul_is_distributive_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int) (z : Int), ((x * (y + z)) = ((x * y) + (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y + z) * x) = ((y * x) + (z * x)))) ∧ (∀ (x : Int) (y : Int) (z : Int), ((x * (y - z)) = ((x * y) - (x * z)))) ∧ (∀ (x : Int) (y : Int) (z : Int), (((y - z) * x) = ((y * x) - (z * x))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_multiplies
      (a : Int) (b : Nat) (c : Nat)
  : (0 ≤ (clip Nat (b * c))) ∧ ((arithmetic.power.pow (arithmetic.power.pow a b) c) = (arithmetic.power.pow a (clip Nat (b * c))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_mul_is_commutative_auto
      («no%param» : Int)
  : (∀ (x : Int) (y : Int), ((x * y) = (y * x)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_distributes
      (a : Int) (b : Int) (e : Nat)
  : ((arithmetic.power.pow (a * b) e) = ((arithmetic.power.pow a e) * (arithmetic.power.pow b e)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_properties_prove_pow_auto
      («no%param» : Int)
  : (∀ (x : Int), ((arithmetic.power.pow x 0) = 1)) ∧ (∀ (x : Int), ((arithmetic.power.pow x 1) = x)) ∧ (∀ (x : Int) (y : Int), ((y = 0) → ((arithmetic.power.pow x (clip Nat y)) = 1))) ∧ (∀ (x : Int) (y : Int), ((y = 1) → ((arithmetic.power.pow x (clip Nat y)) = x))) ∧ (∀ (x : Int) (y : Int), (((0 < x) ∧ (0 < y)) → (x ≤ (x * (clip Nat y))))) ∧ (∀ (x : Int) (y : Int), (((0 < x) ∧ (1 < y)) → (x < (x * (clip Nat y))))) ∧ (∀ (x : Int) (y : Nat) (z : Nat), ((arithmetic.power.pow x (clip Nat (y + z))) = ((arithmetic.power.pow x y) * (arithmetic.power.pow x z)))) ∧ (∀ (x : Int) (y : Nat) (z : Nat), ((y ≥ z) → (((arithmetic.power.pow x (clip Nat (y - z))) * (arithmetic.power.pow x z)) = (arithmetic.power.pow x y)))) ∧ (∀ (x : Int) (y : Nat) (z : Nat), ((arithmetic.power.pow (x * y) z) = ((arithmetic.power.pow x z) * (arithmetic.power.pow y z))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_strictly_increases
      (b : Nat) (e1 : Nat) (e2 : Nat)
      (_0 : (1 < b) := by verus_default_tac) (_1 : (e1 < e2) := by verus_default_tac)
  : ((arithmetic.power.pow b e1) < (arithmetic.power.pow b e2))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_increases
      (b : Nat) (e1 : Nat) (e2 : Nat)
      (_0 : (b > 0) := by verus_default_tac) (_1 : (e1 ≤ e2) := by verus_default_tac)
  : ((arithmetic.power.pow b e1) ≤ (arithmetic.power.pow b e2))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_strictly_increases_converse
      (b : Nat) (e1 : Nat) (e2 : Nat)
      (_0 : (b > 0) := by verus_default_tac) (_1 : ((arithmetic.power.pow b e1) < (arithmetic.power.pow b e2)) := by verus_default_tac)
  : (e1 < e2)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_increases_converse
      (b : Nat) (e1 : Nat) (e2 : Nat)
      (_0 : (1 < b) := by verus_default_tac) (_1 : ((arithmetic.power.pow b e1) ≤ (arithmetic.power.pow b e2)) := by verus_default_tac)
  : (e1 ≤ e2)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pull_out_pows
      (b : Nat) (x : Nat) (y : Nat) (z : Nat)
      (_0 : (b > 0) := by verus_default_tac)
  : (0 ≤ (clip Nat (x * y))) ∧ (0 ≤ (clip Nat (y * z))) ∧ ((arithmetic.power.pow (arithmetic.power.pow b (clip Nat (x * y))) z) = (arithmetic.power.pow (arithmetic.power.pow b x) (clip Nat (y * z))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_division_inequality
      (x : Nat) (b : Nat) (e1 : Nat) (e2 : Nat)
      (_0 : (b > 0) := by verus_default_tac) (_1 : (e2 ≤ e1) := by verus_default_tac) (_2 : (x < (arithmetic.power.pow b e1)) := by verus_default_tac)
  : ((arithmetic.power.pow b e2) > 0) ∧ ((x / (arithmetic.power.pow b e2)) < (arithmetic.power.pow b (clip Nat (e1 - e2))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_mod
      (b : Nat) (e : Nat)
      (_0 : (b > 0) := by verus_default_tac) (_1 : (e > 0) := by verus_default_tac)
  : (((arithmetic.power.pow b e) % b) = 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power.lemma_pow_mod_noop
      (b : Int) (e : Nat) (m : Int)
      (_0 : (m > 0) := by verus_default_tac)
  : (((arithmetic.power.pow (b % m) e) % m) = ((arithmetic.power.pow b e) % m))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_pos
      (e : Nat)
  : ((arithmetic.power2.pow2 e) > 0)
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_pos_auto
      («no%param» : Int)
  : (∀ (e : Nat), ((arithmetic.power2.pow2 e) > 0))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2
      (e : Nat)
  : ((arithmetic.power2.pow2 e) = (arithmetic.power.pow 2 e))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_auto
      («no%param» : Int)
  : (∀ (e : Nat), ((arithmetic.power2.pow2 e) = (arithmetic.power.pow 2 e)))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_adds
      (e1 : Nat) (e2 : Nat)
  : ((arithmetic.power2.pow2 (clip Nat (e1 + e2))) = (clip Nat ((arithmetic.power2.pow2 e1) * (arithmetic.power2.pow2 e2))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_adds_auto
      («no%param» : Int)
  : (∀ (e1 : Nat) (e2 : Nat), ((arithmetic.power2.pow2 (clip Nat (e1 + e2))) = (clip Nat ((arithmetic.power2.pow2 e1) * (arithmetic.power2.pow2 e2)))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_strictly_increases
      (e1 : Nat) (e2 : Nat)
      (_0 : (e1 < e2) := by verus_default_tac)
  : ((arithmetic.power2.pow2 e1) < (arithmetic.power2.pow2 e2))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_strictly_increases_auto
      («no%param» : Int)
  : (∀ (e1 : Nat) (e2 : Nat), ((e1 < e2) → ((arithmetic.power2.pow2 e1) < (arithmetic.power2.pow2 e2))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_mask_div2
      (e : Nat)
      (_0 : (0 < e) := by verus_default_tac)
  : ((((arithmetic.power2.pow2 e) - 1) / 2) = ((arithmetic.power2.pow2 (clip Nat (e - 1))) - 1))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma_pow2_mask_div2_auto
      («no%param» : Int)
  : (∀ (e : Nat), ((0 < e) → ((((arithmetic.power2.pow2 e) - 1) / 2) = ((arithmetic.power2.pow2 (clip Nat (e - 1))) - 1))))
  := by verus_default_tac

@[verus_attr]
theorem arithmetic.power2.lemma2_to64
      («no%param» : Int)
  : ((arithmetic.power2.pow2 0) = 1) ∧ ((arithmetic.power2.pow2 1) = 2) ∧ ((arithmetic.power2.pow2 2) = 4) ∧ ((arithmetic.power2.pow2 3) = 8) ∧ ((arithmetic.power2.pow2 4) = 16) ∧ ((arithmetic.power2.pow2 5) = 32) ∧ ((arithmetic.power2.pow2 6) = 64) ∧ ((arithmetic.power2.pow2 7) = 128) ∧ ((arithmetic.power2.pow2 8) = 256) ∧ ((arithmetic.power2.pow2 9) = 512) ∧ ((arithmetic.power2.pow2 10) = 1024) ∧ ((arithmetic.power2.pow2 11) = 2048) ∧ ((arithmetic.power2.pow2 12) = 4096) ∧ ((arithmetic.power2.pow2 13) = 8192) ∧ ((arithmetic.power2.pow2 14) = 16384) ∧ ((arithmetic.power2.pow2 15) = 32768) ∧ ((arithmetic.power2.pow2 16) = 65536) ∧ ((arithmetic.power2.pow2 17) = 131072) ∧ ((arithmetic.power2.pow2 18) = 262144) ∧ ((arithmetic.power2.pow2 19) = 524288) ∧ ((arithmetic.power2.pow2 20) = 1048576) ∧ ((arithmetic.power2.pow2 21) = 2097152) ∧ ((arithmetic.power2.pow2 22) = 4194304) ∧ ((arithmetic.power2.pow2 23) = 8388608) ∧ ((arithmetic.power2.pow2 24) = 16777216) ∧ ((arithmetic.power2.pow2 25) = 33554432) ∧ ((arithmetic.power2.pow2 26) = 67108864) ∧ ((arithmetic.power2.pow2 27) = 134217728) ∧ ((arithmetic.power2.pow2 28) = 268435456) ∧ ((arithmetic.power2.pow2 29) = 536870912) ∧ ((arithmetic.power2.pow2 30) = 1073741824) ∧ ((arithmetic.power2.pow2 31) = 2147483648) ∧ ((arithmetic.power2.pow2 32) = 4294967296) ∧ ((arithmetic.power2.pow2 64) = 18446744073709551616)
  := by verus_default_tac

