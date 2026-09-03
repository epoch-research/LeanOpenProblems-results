import Submission.UniformPrimeFactorError
import Submission.PrimeFactorErrorScales

/-! Uniform prime-power-factor removal, including the original balanced
Vaughan cutoffs. The Mobius cutoff is unrestricted in the error bound. -/
namespace Erdos972BalancedPrimeFactorErrorScales
open Filter
open scoped Topology
open Erdos972UniformPrimeFactorError Erdos972PrimeFactorError Erdos972PrimeFactorErrorScales
open Erdos972AsymmetricDiagonalBudget Erdos972CenteredRowScales Erdos972CovarianceScaleBudgets
open Erdos972PrimePowerError Erdos972PolynomialRowScales Erdos972GrowingTypeIIReduction
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma smallCutoff_cube_le_balanced {u : ℕ} (hu : 0 < u) :
    mobiusCutoff u^3 ≤ growingCutoff u := by
  have hz := root64_bounds (root64_bounds hu).1
  have hZ : 0 < mobiusCutoff u := hz.1
  have hZ64 : mobiusCutoff u^64 ≤ root64 u := hz.2.1
  apply Nat.le_sqrt'.mpr
  calc
    _ = mobiusCutoff u^6 := by ring
    _ ≤ mobiusCutoff u^64 := Nat.pow_le_pow_right hZ (by norm_num)
    _ ≤ _ := hZ64

lemma smallCutoff_le_balanced {u : ℕ} (hu : 0 < u) :
    mobiusCutoff u ≤ growingCutoff u :=
  (Nat.le_self_pow (by norm_num : 3 ≠ 0) _).trans (smallCutoff_cube_le_balanced hu)

lemma uniform_primeFactorError_scale_fourth {α : ℝ} (hα : 1 ≤ α) {u U V : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hV : mobiusCutoff u^3 ≤ V) :
    |primeFactorError α (scaleCutoff α u) U V /
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
  have hh := primeFactorError_normalized_fourth_general (U := U) hα hN hU hV hiL hoL
  apply hh.trans_eq
  unfold primeFactorBudget
  ring

theorem eventually_small_uniform_prime_factor_error {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ U V : ℕ, mobiusCutoff u^3 ≤ V →
      |primeFactorError α (scaleCutoff α u) U V| ≤
        ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊,
    (tendsto_order.mp (primeFactorBudget_tendsto α)).2 (ε^4) (pow_pos hε 4)] with u hu huα hbudget
  intro U V hV
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hN : 0 < scaleCutoff α u := hu.trans (scaleCutoff_bounds hα hu hαu).1
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hh := (uniform_primeFactorError_scale_fourth (U := U) hα hu hαu hV).trans hbudget.le
  have hsmall := (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le (by norm_num : 4 ≠ 0)).mp hh
  rw [abs_div, abs_of_pos hN0] at hsmall
  exact (div_le_iff₀ hN0).mp hsmall

theorem eventually_small_balanced_prime_factor_error {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      |primeFactorError α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)| ≤
        ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_small_uniform_prime_factor_error hα hε,
    eventually_ge_atTop (1 : ℕ)] with u hu hu0
  exact hu _ _ (smallCutoff_cube_le_balanced hu0)

#print axioms smallCutoff_cube_le_balanced
#print axioms eventually_small_uniform_prime_factor_error
#print axioms eventually_small_balanced_prime_factor_error
end Erdos972BalancedPrimeFactorErrorScales
