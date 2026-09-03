import Submission.StructuredStrictHalfScales
import Submission.PolynomialDensityTransfer

/-!
# A stronger fixed multiplicity exponent from the composite second sieve

All exponents below 1/2 + 1/(8a+2) are obtained, provided a exceeds the
explicit sieve constant. Increasing a shrinks the gain; no exponents
approaching one are supplied by this statement.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma composite_sieve_complementary_exponent (a : ℕ) :
    1 - ((128 * a : ℕ) : ℝ) / ((64 * (4 * a + 1) : ℕ) : ℝ) =
      1 / 2 + 1 / (8 * (a : ℝ) + 2) := by
  have hden : (8 * (a : ℝ) + 2) ≠ 0 := by positivity
  have hden' : 4 * (a : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Fixed polynomial density losses do not affect the limiting exponent. -/
theorem infinite_g_gt_composite_sieved_limit (a : ℕ)
    (hC : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ))
    (γ : ℝ) (hγ : γ < 1 / 2 + 1 / (8 * (a : ℝ) + 2)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64 * (4 * a + 1)) (128 * a)
    1 (structuredPrimeCountConstant (2 * a) (4 * a + 1)) (2 * a + 1) (by omega) ?_ γ
      (by rw [composite_sieve_complementary_exponent]; exact hγ)
  filter_upwards [eventually_strict_structured_smooth_family a hC] with m hm
  obtain ⟨P, hP, hcount⟩ := hm
  refine ⟨P, ?_, hcount⟩
  intro p hp
  have h := hP p hp
  exact ⟨h.1, h.2.1, by simpa only [one_mul] using h.2.2.1⟩

/-- Eliminating the auxiliary natural parameter gives an explicit fixed
threshold. This remains bounded away from one. -/
theorem infinite_g_gt_composite_uniform (γ : ℝ)
    (hγ : γ < 1 / 2 + 1 / (80000000 * Sieve.totientRatioAverageConstant + 10)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  let a := ⌈10000000 * Sieve.totientRatioAverageConstant⌉₊
  have hC0 : 0 ≤ Sieve.totientRatioAverageConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans totientRatioAverageConstant_ge_one
  have hCa : 10000000 * Sieve.totientRatioAverageConstant ≤ (a : ℝ) := Nat.le_ceil _
  have haC : (a : ℝ) ≤ 10000000 * Sieve.totientRatioAverageConstant + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hC0)).le
  apply infinite_g_gt_composite_sieved_limit a hCa γ
  apply hγ.trans_le
  apply _root_.add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith only [haC]

/-- The portion of the original assertion currently obtained by this method. -/
theorem erdos_821_composite_range (ε : ℝ)
    (hε : 1 / 2 - 1 / (80000000 * Sieve.totientRatioAverageConstant + 10) < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  exact infinite_g_gt_composite_uniform (1 - ε) (by linarith only [hε])

lemma composite_uniform_gain_gt_eighty_old_gain :
    80 * (3 / (19327352832 * Sieve.totientRatioAverageConstant + 128)) <
      1 / (80000000 * Sieve.totientRatioAverageConstant + 10) := by
  have hC := totientRatioAverageConstant_ge_one
  have hd : 0 < 19327352832 * Sieve.totientRatioAverageConstant + 128 := by linarith
  have hd' : 0 < 80000000 * Sieve.totientRatioAverageConstant + 10 := by linarith
  rw [show (80 : ℝ) * (3 / (19327352832 * Sieve.totientRatioAverageConstant + 128)) =
    240 / (19327352832 * Sieve.totientRatioAverageConstant + 128) by ring]
  apply (div_lt_div_iff₀ hd hd').mpr
  linarith only [hC]

end Erdos821
