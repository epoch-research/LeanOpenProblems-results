import Submission.PositiveRemainderPrimeCovariance
import Submission.CommonCovarianceScales

/-! The nonlinear positive-remainder / prime covariance is sublinear on
large good scales for each fixed pair of cutoffs. A diagonal existence
statement allows both cutoffs to grow, but does not prescribe a power rate. -/
namespace Erdos972PositiveRemainderPrimeScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PositiveRemainderPrimeCovariance Erdos972GcdProfileExpansion
open Erdos972LipschitzLogWeights Erdos972ChebyshevRowMean
open Erdos972CovarianceScaleBudgets Erdos972CommonCovarianceScales
open Erdos972CenteredRowScales Erdos972PolynomialRowScales Erdos972GrowingTypeI
open Erdos972WeightedBeattyRows Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972DivisorCovariance

noncomputable def positiveCovarianceBudget (α : ℝ) (U V u : ℕ) : ℝ :=
  (U*V:ℕ)*centeredMeanBudget (rowMean α) 1 (scaleCutoff α u)+
    100*(U*V:ℕ)*(profileCost (U*V).factorial+1)*(1+Real.log (α*scaleCutoff α u))^2*
      (polynomialRowError u (root64 u)+1)

lemma positiveCovarianceBudget_nonneg (α : ℝ) (U V u : ℕ) :
    0 ≤ positiveCovarianceBudget α U V u := by
  unfold positiveCovarianceBudget polynomialRowError
  positivity [centeredMeanBudget_nonneg (rowMean α) 1 (scaleCutoff α u),
    profileCost_nonneg (U*V).factorial, Erdos972PrimeRotation.rotationConstant_pos 256,
    Real.log_natCast_nonneg u]

/-- Fixed cutoff means fixed finite pattern cost. No uniform assertion over
power-growing factorial moduli is made here. -/
theorem positiveCovarianceBudget_div_tendsto {α : ℝ} (hα : 1 ≤ α) (U V : ℕ) :
    Tendsto (fun u : ℕ => positiveCovarianceBudget α U V u/scaleCutoff α u) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  let C : ℝ := 100*(U*V:ℕ)*(profileCost (U*V).factorial+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity [profileCost_nonneg (U*V).factorial]
  have hmain := ((centeredMeanBudget_div_tendsto (rowMean α) 1 (rowMean_div_tendsto hα0)).const_mul ((U*V:ℕ):ℝ)).comp
    (scaleCutoff_tendsto hα)
  simp only [mul_zero] at hmain
  have htail := scale_log_weight_tendsto hα 2 hC
    (fun u => polynomialRowError u (root64 u)+1)
    (by intro u; unfold polynomialRowError; positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u])
    (summed_polynomialRowError_add_one_tendsto 2)
  have hsum := hmain.add htail
  simp only [add_zero] at hsum
  apply squeeze_zero_norm' _ hsum
  filter_upwards [eventually_ge_atTop (1:ℕ)] with u hu
  have hv : (1:ℝ) ≤ root64 u := by exact_mod_cast (root64_bounds hu).1
  have hE : 0 ≤ polynomialRowError u (root64 u)+1 := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (positiveCovarianceBudget_nonneg α U V u) (Nat.cast_nonneg _))]
  unfold positiveCovarianceBudget
  rw [add_div, mul_div_assoc]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hv
    (mul_nonneg (mul_nonneg hC (sq_nonneg (1+Real.log (α*scaleCutoff α u)))) hE)
  dsimp only [C] at hh ⊢
  nlinarith only [hh]

/-- An unconditional eventual implication on the already proved good-row
scales. This is a signed covariance estimate, not an unsigned energy bound. -/
theorem eventually_positive_remainder_prime_covariance {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 0 < V) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, OutputPrimeScale α u →
      |covariance (scaleCutoff α u) (positiveRemainder U V)
        (fun n => Λ (floorMul α n))| ≤ ε*(scaleCutoff α u : ℝ) := by
  have hb := eventually_bound_of_scaled_limit hα.le (positiveCovarianceBudget α U V)
    (positiveCovarianceBudget_div_tendsto hα.le U V) hε
  filter_upwards [hb, root64_tendsto.eventually_ge_atTop (U*V).factorial,
    (scaleCutoff_tendsto hα.le).eventually_ge_atTop (U*V)] with u hbudget hF hN
  intro hrows
  have hE : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hh := positive_remainder_prime_covariance_bound hα hI hE hU hV hN (by
    intro d hd Q hQ
    rw [outputRow_mangoldt]
    exact hrows d (Nat.pos_of_mem_divisors hd)
      ((Nat.le_of_dvd (Nat.factorial_pos _) (Nat.dvd_of_mem_divisors hd)).trans hF)
      Q (hQ.trans (scaleCutoff_row_eligible hα.le u d (scaleCutoff α u/d) le_rfl)))
  exact hh.trans hbudget

/-- For each requested lower bound on both cutoffs and the scale, there is
an actual good scale with small positive-remainder / prime covariance.
The chosen cutoff is fixed before that scale is selected. -/
theorem exists_growing_positive_remainder_prime_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ W u N : ℕ, B < W ∧ B < u ∧ N = scaleCutoff α u ∧
      (W*W).factorial ≤ root64 u ∧ OutputPrimeScale α u ∧
      |covariance N (positiveRemainder W W) (fun n => Λ (floorMul α n))| ≤ ε*(N:ℝ) := by
  let W := B+1
  have hW : 0 < W := by dsimp [W]; omega
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_positive_remainder_prime_covariance hα hI hW hW hε).and
      (root64_tendsto.eventually_ge_atTop (W*W).factorial))
  obtain ⟨u, hu, hαu, hv, hrows, hdiv⟩ := exists_joint_prime_divisor_scale hα hI (max B T)
  obtain ⟨hcov, hF⟩ := hT u ((le_max_right B T).trans hu.le)
  exact ⟨W, u, scaleCutoff α u, by dsimp [W]; omega,
    (le_max_left B T).trans_lt hu, rfl, hF, hrows, hcov hrows⟩

#print axioms positiveCovarianceBudget_div_tendsto
#print axioms eventually_positive_remainder_prime_covariance
#print axioms exists_growing_positive_remainder_prime_scale

end Erdos972PositiveRemainderPrimeScales
