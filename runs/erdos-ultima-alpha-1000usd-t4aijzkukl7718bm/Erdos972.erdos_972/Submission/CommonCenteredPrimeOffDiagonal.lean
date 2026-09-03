import Submission.CenteredPrimeFactorScales
import Submission.CommonBalancedOffDiagonal

/-! The common-scale off-diagonal reduction with the actual prime-restricted
means in its centering. No strict signed lower gap is proved here. -/
namespace Erdos972CommonCenteredPrimeOffDiagonal
open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972CenteredPrimeFactorError Erdos972CenteredPrimeFactorScales
open Erdos972CommonBalancedOffDiagonal Erdos972CommonCovarianceScales
open Erdos972FourFactorDiagonalSplit Erdos972PrimeFactorRemainder
open Erdos972CovarianceScaleBudgets Erdos972TypeICovarianceScales
open Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972GrowingTypeI Erdos972GrowingTypeIIReduction Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972LogarithmicCovariance Erdos972DoubleVaughan Erdos972PrimePowerError Erdos972CenteredDoubleVaughan
open Erdos972OriginalTypeICovariance Erdos972DualTypeICovariance Erdos972TypeICovariance
open Erdos972WeightedBeattyRows Erdos972WeightedPrimeRotation Erdos972BeattyRows
set_option maxHeartbeats 1500000
set_option autoImplicit false
attribute [local irreducible] root64

noncomputable def centeredPrimeOffDiagonal (α : ℝ) (N U V : ℕ) : ℝ :=
  primeFactorOffDiagonal α N U V -
    total N (primeTypeIIPart U V)*total N (fun n => primeTypeIIPart U V (floorMul α n))/(N : ℝ)

lemma centered_prime_remainder_split {α : ℝ} (hα : 1 ≤ α) (N U V : ℕ) :
    centeredPrimeRemainder α N U V =
      primeVaughanDiagonal α N U V + centeredPrimeOffDiagonal α N U V := by
  unfold centeredPrimeRemainder covariance centeredPrimeOffDiagonal
  change pairSum α N (primeTypeIIPart U V) (primeTypeIIPart U V) - _ = _
  rw [prime_remainder_diagonal_split hα]
  ring

lemma centered_prime_offDiagonal_removal_identity {α : ℝ} (hα : 1 ≤ α) (N U V : ℕ) :
    centeredFourFactor α N U V U V - centeredPrimeOffDiagonal α N U V =
      primeVaughanDiagonal α N U V + centeredPrimeFactorError α N U V := by
  unfold centeredPrimeFactorError
  rw [centered_prime_remainder_split hα]
  ring

/-- The three Type-I errors and the replacement of the entire four-factor
remainder by its distinct-prime-factor off-diagonal are small at one scale. -/
theorem exists_balanced_typeI_and_centered_prime_offDiagonal_scale {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ root64 u ≤ N ∧
      growingCutoff u * growingCutoff u ≤ root64 u ∧ OutputPrimeScale α u ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N ∧
      |centeredFourFactor α N (growingCutoff u) (growingCutoff u)
        (growingCutoff u) (growingCutoff u) -
        centeredPrimeOffDiagonal α N (growingCutoff u) (growingCutoff u)| ≤ ε*N := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_original_covariance_budget hα.le hε).and
      ((eventually_dual_covariance_budget hα.le hε).and
        ((eventually_double_typeI_budget hα.le hε).and
          (eventually_small_balanced_centered_prime_factor_error hα.le (show 0 < ε/2 by positivity)))))
  obtain ⟨u, hu, hcut, hαu, hv, hrows, hdual, hdiv, hdiag⟩ :=
    exists_two_sided_scale_small_balanced_diagonal hα hI (show 0 < ε/2 by positivity) (max B T)
  obtain ⟨hl, hr, hd, hpower⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα.le hu0 hαu'
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  have hU0 : 0 < growingCutoff u := (Nat.zero_le _).trans_lt hcut
  have hV0 := hU0
  have helig := (growingCutoff_eligible u).2
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hEp0 : 0 ≤ scaledRowError (dualScaleLoss α) u (root64 u) := by
    unfold scaledRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hEd0 : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4 := by positivity
  refine ⟨u, scaleCutoff α u, (le_max_left B T).trans_lt hu, rfl,
    (le_max_left B T).trans_lt hcut, hvN, helig, hrows, ?_, ?_, ?_, ?_⟩
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

  · rw [centered_prime_offDiagonal_removal_identity hα.le]
    exact (abs_add_le _ _).trans ((add_le_add hdiag hpower).trans_eq (by ring))

#print axioms centered_prime_remainder_split
#print axioms centered_prime_offDiagonal_removal_identity
#print axioms exists_balanced_typeI_and_centered_prime_offDiagonal_scale
end Erdos972CommonCenteredPrimeOffDiagonal
