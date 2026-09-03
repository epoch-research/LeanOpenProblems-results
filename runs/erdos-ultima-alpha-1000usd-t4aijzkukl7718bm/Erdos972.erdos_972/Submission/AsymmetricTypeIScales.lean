import Submission.CommonAsymmetricDiagonal

/-! All Type-I covariance errors and the equal-factor diagonal are small on
one common scale with unequal cutoffs. The off-diagonal gap remains open. -/
namespace Erdos972AsymmetricTypeIScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972AsymmetricDiagonalBudget Erdos972CommonAsymmetricDiagonal
open Erdos972VaughanDiagonalBound Erdos972CommonCovarianceScales
open Erdos972CovarianceScaleBudgets Erdos972TypeICovarianceScales
open Erdos972MobiusPartialSums Erdos972MobiusLaplace
open Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972GrowingTypeI Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972LogarithmicCovariance Erdos972DoubleVaughan Erdos972PrimePowerError
open Erdos972OriginalTypeICovariance Erdos972DualTypeICovariance Erdos972TypeICovariance
open Erdos972WeightedBeattyRows Erdos972WeightedPrimeRotation Erdos972BeattyRows

set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma eventually_asymmetric_double_budget {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      32*(scaleCutoff α u : ℝ)*|reciprocalMoebius (mobiusCutoff u)*reciprocalMoebius (mobiusCutoff u)|+
        100*(118*(root64 u : ℝ)*(u : ℝ)^4+1)*(root64 u : ℝ)^2*
          (1+Real.log (α*scaleCutoff α u))^5 ≤ ε*(scaleCutoff α u : ℝ) := by
  have hm := reciprocalMoebius_tendsto_zero.comp mobiusCutoff_tendsto
  have hprod : Tendsto (fun u : ℕ => 32*|reciprocalMoebius (mobiusCutoff u)*reciprocalMoebius (mobiusCutoff u)|)
      atTop (𝓝 0) := by
    simpa using ((hm.mul hm).abs.const_mul 32)
  filter_upwards [eventually_covariance_budget hα (show 0 < ε/2 by positivity),
    (tendsto_order.mp hprod).2 (ε/2) (by positivity)] with u he hm
  have hh := mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg (α := ℝ) (scaleCutoff α u))
  nlinarith only [he, hh]

/-- The cutoffs and all four small error terms use the same u and N. -/
theorem exists_asymmetric_typeI_and_diagonal_scale {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < mobiusCutoff u ∧ root64 u ≤ N ∧
      mobiusCutoff u * mangoldtCutoff u ≤ root64 u ∧ OutputPrimeScale α u ∧
      |covariance N (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) n)
        (fun n => typeIPart (mobiusCutoff u) (mangoldtCutoff u) (floorMul α n))| ≤ ε*N ∧
      |vaughanDiagonal α N (mobiusCutoff u) (mangoldtCutoff u)| ≤ ε*N := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_original_covariance_budget hα.le hε).and
      ((eventually_dual_covariance_budget hα.le hε).and
        (eventually_asymmetric_double_budget hα.le hε)))
  obtain ⟨u, hu, hcut, hαu, hv, hrows, hdual, hdiv, hdiag⟩ :=
    exists_two_sided_scale_small_diagonal hα hI hε (max B T)
  obtain ⟨hl, hr, hd⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα.le hu0 hαu'
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  obtain ⟨hU0, helig, hUu⟩ := asymmetric_cutoffs_bounds hu0
  have hV0 : 0 < mangoldtCutoff u := by unfold mangoldtCutoff; positivity
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hEp0 : 0 ≤ scaledRowError (dualScaleLoss α) u (root64 u) := by
    unfold scaledRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hEd0 : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4 := by positivity
  refine ⟨u, scaleCutoff α u, (le_max_left B T).trans_lt hu, rfl,
    (le_max_left B T).trans_lt hcut, hvN, helig, hrows, ?_, ?_, ?_, hdiag⟩
  · have hh := original_typeI_covariance_bound hα hI hE0 hU0 hV0 helig hvN (by
      intro m hm hmv X hX
      rw [outputRow_mangoldt]
      exact hrows m hm hmv X (hX.trans (scaleCutoff_row_eligible hα.le u m (scaleCutoff α u/m) le_rfl)))
    exact hh.trans hl
  · have hh := dual_typeI_covariance_bound hα.le hU0 hV0 helig hvN hEp0 hEd0 (by
      intro j hj e he
      exact hdual e (mem_Ioc.mp he).1 ((mem_Ioc.mp he).2.trans helig) j (hj.trans hNu)) (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hr
  · have hh := typeI_covariance_bound hα.le hU0 hV0 hU0 hV0 helig helig hvN hEd0 (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hd

#print axioms eventually_asymmetric_double_budget
#print axioms exists_asymmetric_typeI_and_diagonal_scale

end Erdos972AsymmetricTypeIScales
