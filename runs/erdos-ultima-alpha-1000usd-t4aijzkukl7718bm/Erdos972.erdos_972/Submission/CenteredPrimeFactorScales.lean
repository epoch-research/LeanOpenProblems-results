import Submission.CenteredPrimeFactorError
import Submission.BalancedPrimeFactorErrorScales

/-! Uniform o(N) control for the fully centered prime-power-factor error,
including both remainder means, on the original balanced scales. -/
namespace Erdos972CenteredPrimeFactorScales
open Filter
open scoped Topology
open Erdos972CenteredPrimeFactorError Erdos972BalancedPrimeFactorErrorScales
open Erdos972AsymmetricDiagonalBudget Erdos972CenteredRowScales Erdos972CovarianceScaleBudgets
open Erdos972PrimePowerError Erdos972PolynomialRowScales Erdos972GrowingTypeIIReduction
set_option maxHeartbeats 1500000
set_option autoImplicit false
attribute [local irreducible] root64

noncomputable def centeredPrimeFactorBudget (α : ℝ) (u : ℕ) : ℝ :=
  4096*α^4*(6^19*(1+Real.log u)^19/(mobiusCutoff u : ℝ))^2

lemma centeredPrimeFactorBudget_tendsto (α : ℝ) :
    Tendsto (centeredPrimeFactorBudget α) atTop (𝓝 0) := by
  have hh := ((cutoff_log_div_tendsto (6^19) (by positivity) 19).pow 2).const_mul (4096*α^4)
  simpa only [centeredPrimeFactorBudget, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hh

lemma uniform_centeredPrimeFactorError_scale_fourth {α : ℝ} (hα : 1 ≤ α) {u U V : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hV : mobiusCutoff u^3 ≤ V) :
    |centeredPrimeFactorError α (scaleCutoff α u) U V /
      (scaleCutoff α u : ℝ)|^4 ≤ centeredPrimeFactorBudget α u := by
  let N := scaleCutoff α u
  have hN : 0 < N := hu.trans_le (scaleCutoff_bounds hα hu hαu).1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hU := (asymmetric_cutoffs_bounds hu).1
  have hscale := scale_log_bound hα hu hαu
  have hiL : 1+Real.log N ≤ 6*(1+Real.log u) := by
    have hh := Real.log_le_log hN0 (le_mul_of_one_le_left hN0.le hα)
    exact (show (1 : ℝ)+_ ≤ 1+_ from add_le_add le_rfl hh).trans hscale.2
  have hoL : 1+Real.log (floorMul α N) ≤ 6*(1+Real.log u) := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα hN))
      (floorMul_le_real hα (le_refl N))
    exact (show (1 : ℝ)+_ ≤ 1+_ from add_le_add le_rfl hh).trans hscale.2
  have hh := centered_error_normalized_fourth (U := U) hα hN hU hV hiL hoL
  apply hh.trans_eq
  unfold centeredPrimeFactorBudget
  ring

theorem eventually_small_uniform_centered_prime_factor_error {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ U V : ℕ, mobiusCutoff u^3 ≤ V →
      |centeredPrimeFactorError α (scaleCutoff α u) U V| ≤
        ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊,
    (tendsto_order.mp (centeredPrimeFactorBudget_tendsto α)).2 (ε^4) (pow_pos hε 4)] with u hu huα hbudget
  intro U V hV
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hN : 0 < scaleCutoff α u := hu.trans (scaleCutoff_bounds hα hu hαu).1
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hh := (uniform_centeredPrimeFactorError_scale_fourth (U := U) hα hu hαu hV).trans hbudget.le
  have hsmall := (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le (by norm_num : 4 ≠ 0)).mp hh
  rw [abs_div, abs_of_pos hN0] at hsmall
  exact (div_le_iff₀ hN0).mp hsmall

theorem eventually_small_balanced_centered_prime_factor_error {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      |centeredPrimeFactorError α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)| ≤
        ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_small_uniform_centered_prime_factor_error hα hε,
    eventually_ge_atTop (1 : ℕ)] with u hu hu0
  exact hu _ _ (smallCutoff_cube_le_balanced hu0)

#print axioms centeredPrimeFactorBudget_tendsto
#print axioms eventually_small_uniform_centered_prime_factor_error
#print axioms eventually_small_balanced_centered_prime_factor_error
end Erdos972CenteredPrimeFactorScales
