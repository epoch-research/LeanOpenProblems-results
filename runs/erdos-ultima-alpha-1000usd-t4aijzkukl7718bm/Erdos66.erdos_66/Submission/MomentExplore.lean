import FormalConjecturesUtil

/-!
# Moment constraints on finite self-convolutions

These constraints may help distinguish integer prefixes from flat finite groups.
They do not settle Erdős Problem 66.
-/

namespace Erdos66Moment

variable {X : Type*} (A : Finset X) (x : X → ℝ)

lemma pair_second_moment (hzero : ∑ a ∈ A, x a = 0) :
    (∑ a ∈ A, ∑ b ∈ A, (x a + x b) ^ 2) =
      2 * (A.card : ℝ) * ∑ a ∈ A, (x a) ^ 2 := by
  simp only [add_sq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hzero, mul_zero, zero_mul, add_zero, zero_add]
  ring

lemma pair_fourth_moment (hzero : ∑ a ∈ A, x a = 0) :
    (∑ a ∈ A, ∑ b ∈ A, (x a + x b) ^ 4) =
      2 * (A.card : ℝ) * (∑ a ∈ A, (x a) ^ 4) + 6 * (∑ a ∈ A, (x a) ^ 2) ^ 2 := by
  have hp (a b : X) : (x a + x b) ^ 4 =
      (x a) ^ 4 + 4 * (x a) ^ 3 * x b + 6 * (x a) ^ 2 * (x b) ^ 2 +
        4 * x a * (x b) ^ 3 + (x b) ^ 4 := by ring
  simp only [hp, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hzero, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- The kurtosis of a sum of two independent copies is at least two.
The formula uses finite sums to avoid any probabilistic prerequisites. -/
lemma pair_kurtosis_bound (hzero : ∑ a ∈ A, x a = 0) :
    2 * (∑ a ∈ A, ∑ b ∈ A, (x a + x b) ^ 2) ^ 2 ≤
      (A.card : ℝ) ^ 2 * (∑ a ∈ A, ∑ b ∈ A, (x a + x b) ^ 4) := by
  have hc : (∑ a ∈ A, (x a) ^ 2) ^ 2 ≤
      (A.card : ℝ) * ∑ a ∈ A, (x a) ^ 4 := by
    have hh := sq_sum_le_card_mul_sum_sq (s := A) (f := fun a ↦ (x a) ^ 2)
    simp_rw [← pow_mul] at hh
    norm_num at hh
    exact hh
  rw [pair_second_moment A x hzero, pair_fourth_moment A x hzero]
  nlinarith [mul_nonneg (sq_nonneg (A.card : ℝ)) (sub_nonneg.mpr hc)]

lemma center_sum_zero :
    ∑ a ∈ A, (x a - (∑ b ∈ A, x b) / A.card) = 0 := by
  by_cases hA : A.card = 0
  · simp only [Finset.card_eq_zero.mp hA, Finset.sum_empty]
  · have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring

lemma centered_pair_kurtosis_bound :
    2 * (∑ a ∈ A, ∑ b ∈ A,
        (x a + x b - 2 * (∑ c ∈ A, x c) / A.card) ^ 2) ^ 2 ≤
      (A.card : ℝ) ^ 2 * (∑ a ∈ A, ∑ b ∈ A,
        (x a + x b - 2 * (∑ c ∈ A, x c) / A.card) ^ 4) := by
  have h := pair_kurtosis_bound A (fun a ↦ x a - (∑ c ∈ A, x c) / A.card) (center_sum_zero A x)
  have he (a b : X) : (x a - (∑ c ∈ A, x c) / A.card) +
      (x b - (∑ c ∈ A, x c) / A.card) = x a + x b - 2 * (∑ c ∈ A, x c) / A.card := by ring
  simpa only [he] using h

end Erdos66Moment
