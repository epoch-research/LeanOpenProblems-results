import Submission.PrimeInverseLogMoments

/-! Prime sums of affine functions of the first-hit logarithmic ratio.
The error is explicit and uniform in the main scale. -/
namespace Erdos970.WeightedMertens
open Finset Real

noncomputable def affineRatioPrimeInterval (L A B x y : ℝ) : ℝ :=
  ∑ p ∈ Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime,
    (A + B * ((L / log (p : ℝ) - 1) / 2)) / ((p : ℝ) * log p)

lemma affineRatioPrimeInterval_eq (L A B x y : ℝ) :
    affineRatioPrimeInterval L A B x y =
      (A - B / 2) * inverseLogPrimeInterval 0 x y +
        (B * L / 2) * inverseLogPrimeInterval 1 x y := by
  unfold affineRatioPrimeInterval inverseLogPrimeInterval
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  norm_num only [Nat.reduceAdd, pow_one]
  ring

lemma affineRatioPrimeInterval_error (L A B x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    |affineRatioPrimeInterval L A B x y -
      ((A - B / 2) * (1 / log x - 1 / log y) +
        (B * L / 2) * ((1 / log x ^ 2 - 1 / log y ^ 2) / 2))| ≤
      |A - B / 2| * (2 * (boundConstant + 1) / log x ^ 2) +
        |B * L / 2| * (2 * (boundConstant + 1) / log x ^ 3) := by
  have h0 := abs_inverseLogPrimeInterval_sub 0 hx hxy
  have h1 := abs_inverseLogPrimeInterval_sub 1 hx hxy
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, zero_add, one_add_one_eq_two,
    pow_one, div_one] at h0 h1
  rw [affineRatioPrimeInterval_eq]
  have he : (A - B / 2) * inverseLogPrimeInterval 0 x y +
      (B * L / 2) * inverseLogPrimeInterval 1 x y -
        ((A - B / 2) * (1 / log x - 1 / log y) +
          (B * L / 2) * ((1 / log x ^ 2 - 1 / log y ^ 2) / 2)) =
      (A - B / 2) * (inverseLogPrimeInterval 0 x y - (1 / log x - 1 / log y)) +
        (B * L / 2) * (inverseLogPrimeInterval 1 x y -
          (1 / log x ^ 2 - 1 / log y ^ 2) / 2) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))

/-- In logarithmic ratio coordinates, an affine chord has its exact
trapezoidal main term and an O(1/L^2) error with a displayed constant. -/
theorem affineRatioPrimeInterval_scaled_error (L A B a b : ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsmall : (2 * b + 1) * log 2 ≤ L) :
    |affineRatioPrimeInterval L A B (exp (L / (2 * b + 1))) (exp (L / (2 * a + 1))) -
      (b - a) * (2 * A + B * (a + b)) / L| ≤
      (boundConstant + 1) / L ^ 2 *
        (2 * |A - B / 2| * (2 * b + 1) ^ 2 + |B| * (2 * b + 1) ^ 3) := by
  have hda : 0 < 2 * a + 1 := by linarith
  have hdb : 0 < 2 * b + 1 := by linarith
  have hx : (2 : ℝ) ≤ exp (L / (2 * b + 1)) := by
    calc
      (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
      _ ≤ exp (L / (2 * b + 1)) := exp_le_exp.mpr ((le_div_iff₀ hdb).mpr (by nlinarith only [hsmall]))
  have hxy : exp (L / (2 * b + 1)) ≤ exp (L / (2 * a + 1)) := by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL.le hda (by linarith)
  have hh := affineRatioPrimeInterval_error L A B _ _ hx hxy
  rw [log_exp, log_exp] at hh
  have hmain : (A - B / 2) * (1 / (L / (2 * b + 1)) - 1 / (L / (2 * a + 1))) +
      (B * L / 2) * ((1 / (L / (2 * b + 1)) ^ 2 - 1 / (L / (2 * a + 1)) ^ 2) / 2) =
        (b - a) * (2 * A + B * (a + b)) / L := by
    field_simp
    <;> ring
  rw [hmain] at hh
  convert hh using 1
  rw [abs_div, abs_mul, abs_of_pos hL]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  <;> ring

#print axioms affineRatioPrimeInterval_scaled_error
end Erdos970.WeightedMertens
