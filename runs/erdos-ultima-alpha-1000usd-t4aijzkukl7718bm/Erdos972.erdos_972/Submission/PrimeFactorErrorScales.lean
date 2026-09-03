import Submission.PrimeFactorError
import Submission.AsymmetricTypeIScales

/-! Proper-prime-power factors in the double Vaughan remainder contribute
o(N) at the existing asymmetric cutoffs, on every sufficiently large scale.
The remaining signed distinct-prime-factor sum is not controlled here. -/
namespace Erdos972PrimeFactorErrorScales

open Filter
open scoped Topology
open Erdos972PrimeFactorError Erdos972PrimeFactorRemainder Erdos972DoubleVaughan
open Erdos972PrimePowerError Erdos972CenteredRowScales
open Erdos972AsymmetricDiagonalBudget Erdos972CovarianceScaleBudgets
open Erdos972PolynomialRowScales Erdos972AsymmetricTypeIScales
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

noncomputable def primeFactorBudget (α : ℝ) (u : ℕ) : ℝ :=
  16*α*(1+α)^2*(6^19*(1+Real.log u)^19/(mobiusCutoff u : ℝ))^2

lemma primeFactorBudget_tendsto (α : ℝ) :
    Tendsto (primeFactorBudget α) atTop (𝓝 0) := by
  have hh := ((cutoff_log_div_tendsto (6^19) (by positivity) 19).pow 2).const_mul
    (16*α*(1+α)^2)
  simpa only [primeFactorBudget, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hh

lemma primeFactorError_scale_fourth {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) :
    |primeFactorError α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u) /
      (scaleCutoff α u : ℝ)|^4 ≤ primeFactorBudget α u := by
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
  have hh := primeFactorError_normalized_fourth hα hN hU (le_refl (mobiusCutoff u^3)) hiL hoL
  change |primeFactorError α N (mobiusCutoff u) (mobiusCutoff u^3)/(N : ℝ)|^4 ≤ _ at hh
  apply hh.trans_eq
  unfold primeFactorBudget
  ring

theorem eventually_small_prime_factor_error {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      |primeFactorError α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| ≤
        ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊,
    (tendsto_order.mp (primeFactorBudget_tendsto α)).2 (ε^4) (pow_pos hε 4)] with u hu huα hbudget
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hN : 0 < scaleCutoff α u := hu.trans (scaleCutoff_bounds hα hu hαu).1
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hh := (primeFactorError_scale_fourth hα hu hαu).trans hbudget.le
  have hsmall := (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le (by norm_num : 4 ≠ 0)).mp hh
  rw [abs_div, abs_of_pos hN0] at hsmall
  exact (div_le_iff₀ hN0).mp hsmall

#print axioms primeFactorBudget_tendsto
#print axioms primeFactorError_scale_fourth
#print axioms eventually_small_prime_factor_error
end Erdos972PrimeFactorErrorScales
