import Submission.CenteredDoubleVaughan

/-! A finite prime-pair set forces the full prime covariance close to -N
on the same scales used for all Type-I estimates. -/
namespace Erdos972PrimeCovarianceObstruction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance Erdos972ChebyshevRowMean
open Erdos972CovarianceScaleBudgets Erdos972CommonCovarianceScales
open Erdos972CenteredRowScales Erdos972PolynomialRowScales Erdos972GrowingTypeI
open Erdos972WeightedBeattyRows Erdos972MovingCenteredRows Erdos972CorrelationVaughan
open Erdos972TypeIIReduction Erdos972Topology Erdos972DualProfileCovariance

set_option maxHeartbeats 1000000

lemma output_row_error_budget_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u : ℕ => (polynomialRowError u (root64 u)+2*Real.log (α*scaleCutoff α u)+7)/
      (scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
  have hh := scale_log_weight_tendsto hα 1 (by norm_num : (0 : ℝ) ≤ 8)
    (fun u => polynomialRowError u (root64 u)+1)
    (by intro u; unfold polynomialRowError; positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u])
    (summed_polynomialRowError_add_one_tendsto 1)
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hL := (scale_log_bound hα hu hαu).1
  have hv : (1 : ℝ) ≤ root64 u := by exact_mod_cast (root64_bounds hu).1
  have hE : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hlog : 0 ≤ Real.log (α*scaleCutoff α u) := by linarith only [hL]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hp : polynomialRowError u (root64 u)+2*Real.log (α*scaleCutoff α u)+7 ≤
      8*(1+Real.log (α*scaleCutoff α u))*(polynomialRowError u (root64 u)+1) := by
    nlinarith only [hE, hlog, mul_nonneg hE hlog]
  have hm := mul_le_mul_of_nonneg_right hv
    (show 0 ≤ 8*(1+Real.log (α*scaleCutoff α u))*(polynomialRowError u (root64 u)+1) by positivity)
  simp only [pow_one]
  nlinarith only [hp, hm]

lemma output_total_error {α : ℝ} (hα : 1 < α) (hI : Irrational α) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hrows : OutputPrimeScale α u) :
    |total (scaleCutoff α u) (fun n => vonMangoldt (floorMul α n))-
      commonMean α (scaleCutoff α u)*scaleCutoff α u| ≤
        polynomialRowError u (root64 u)+2*Real.log (α*scaleCutoff α u)+7 := by
  have hN : 0 < scaleCutoff α u := hu.trans_le (scaleCutoff_bounds hα.le hu hαu).1
  have hα0 : 0 < α := by linarith
  have hy : 1 ≤ α*scaleCutoff α u := one_le_mul_of_one_le_of_one_le hα.le (by exact_mod_cast hN)
  have hR : |outputRow α (fun q => vonMangoldt q) (floorMul α (scaleCutoff α u))-
      (1/α)*Chebyshev.psi (floorMul α (scaleCutoff α u))| ≤ polynomialRowError u (root64 u) := by
    rw [outputRow_mangoldt]
    have he := scaleCutoff_row_eligible hα.le u 1 (scaleCutoff α u) (by simp)
    simp only [Nat.cast_one, mul_one] at he
    simpa only [Nat.cast_one, mul_one] using hrows 1 (by norm_num) (root64_bounds hu).1 _ he
  have hh := common_centered_row hα hI hy (scaleCutoff α u) le_rfl (by nlinarith only [hα0]) hR
  have he : (∑ n ∈ Ioc 0 (scaleCutoff α u),
      (vonMangoldt (floorMul α n)-Chebyshev.psi (α*scaleCutoff α u)/(α*scaleCutoff α u))) =
      total (scaleCutoff α u) (fun n => vonMangoldt (floorMul α n))-
        commonMean α (scaleCutoff α u)*scaleCutoff α u := by
    simp only [total, commonMean, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    ring
  rwa [he] at hh

lemma eventually_output_mean_error {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, OutputPrimeScale α u →
      |total (scaleCutoff α u) (fun n => vonMangoldt (floorMul α n))/(scaleCutoff α u : ℝ)-
        commonMean α (scaleCutoff α u)| ≤ ε := by
  filter_upwards [(tendsto_order.mp (output_row_error_budget_tendsto hα.le)).2 ε hε,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u he hu huα
  intro hrows
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu.trans (scaleCutoff_bounds hα.le hu hαu).1)
  have hh := div_le_div_of_nonneg_right (output_total_error hα hI hu hαu hrows) hNR.le
  have hid (a b : ℝ) : a/(scaleCutoff α u : ℝ)-b = (a-b*scaleCutoff α u)/(scaleCutoff α u : ℝ) := by
    field_simp
  rw [hid, abs_div, abs_of_nonneg hNR.le]
  exact hh.trans he.le

/-- The main negative covariance obstruction, valid on every sufficiently
large good scale of any hypothetical counterexample. -/
theorem finite_primeSet_forces_negative_prime_covariance {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hfin : (primeSet α).Finite) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, OutputPrimeScale α u →
      |covariance (scaleCutoff α u) (fun n => vonMangoldt n) (fun n => vonMangoldt (floorMul α n))/
        (scaleCutoff α u : ℝ)+1| ≤ ε := by
  have hc := finite_primeSet_correlation_tendsto_zero hα.le hfin
  have hm := centered_main_div_tendsto (show 0 < α by linarith)
  have hlim : Tendsto (fun N : ℕ => mangoldtCorrelation α N/N-commonMean α N*Chebyshev.psi N/N+1)
      atTop (𝓝 0) := by simpa using (hc.sub hm).add_const 1
  have hlim' := (hlim.comp (scaleCutoff_tendsto hα.le)).abs
  simp only [Function.comp_apply, abs_zero] at hlim'
  filter_upwards [(tendsto_order.mp hlim').2 (ε/2) (by positivity),
    eventually_output_mean_error hα hI (show 0 < ε/14 by positivity),
    (scaleCutoff_tendsto hα.le).eventually_ge_atTop 1] with u he hr hN
  intro hrows
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hrow := hr hrows
  have hid : covariance (scaleCutoff α u) (fun n => vonMangoldt n) (fun n => vonMangoldt (floorMul α n))/
      (scaleCutoff α u : ℝ)+1 =
      (mangoldtCorrelation α (scaleCutoff α u)/(scaleCutoff α u : ℝ)-
        commonMean α (scaleCutoff α u)*Chebyshev.psi (scaleCutoff α u)/(scaleCutoff α u : ℝ)+1)-
      (Chebyshev.psi (scaleCutoff α u)/(scaleCutoff α u : ℝ))*
        (total (scaleCutoff α u) (fun n => vonMangoldt (floorMul α n))/(scaleCutoff α u : ℝ)-
          commonMean α (scaleCutoff α u)) := by
    rw [covariance, total_mangoldt]
    change _ = _
    unfold mangoldtCorrelation total
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (psi_ratio_bounds hNR).1]
  have hp := mul_le_mul (psi_ratio_bounds hNR).2 hrow (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
  linarith only [he, hp]

#print axioms finite_primeSet_forces_negative_prime_covariance

end Erdos972PrimeCovarianceObstruction
