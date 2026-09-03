import Submission.CovarianceScaleBudgets

/-! All three Type-I covariance errors vanish at the same scales. -/
namespace Erdos972CommonCovarianceScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972PolynomialRowScales Erdos972CenteredRowScales
open Erdos972GrowingTypeI Erdos972GrowingTypeIIReduction Erdos972CovarianceScaleBudgets
open Erdos972WeightedPrimeRotation Erdos972BeattyRows Erdos972DualPrimeRows
open Erdos972ScaledPrimeRows Erdos972OriginalTypeICovariance Erdos972DualTypeICovariance
open Erdos972TypeICovariance Erdos972LogarithmicCovariance Erdos972DoubleVaughan
open Erdos972WeightedBeattyRows

set_option maxHeartbeats 1000000

def OutputPrimeScale (α : ℝ) (u : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
    |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
      (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u (root64 u)

/-- A simultaneous three-error estimate. In particular the scales in the
three covariance bounds are not selected independently. -/
theorem exists_common_typeI_covariance_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ root64 u ≤ N ∧
      OutputPrimeScale α u ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N ∧
      |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))| ≤ ε*N := by
  have hevent := (eventually_original_covariance_budget hα.le hε).and
    ((eventually_dual_covariance_budget hα.le hε).and
      ((eventually_double_typeI_budget hα.le hε).and (growingCutoff_tendsto.eventually_gt_atTop B)))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  obtain ⟨u, hu, hαu, hv, hrows, hdual, hdiv⟩ := exists_two_sided_prime_divisor_scale hα hI (max B T)
  obtain ⟨hl, hr, hd, hcut⟩ := hT u ((le_max_right B T).trans hu.le)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  obtain ⟨huN, hNu, _⟩ := scaleCutoff_bounds hα.le hu0 hαu'
  have hvN : root64 u ≤ scaleCutoff α u := (root64_le u).trans huN
  have hcut0 : 0 < growingCutoff u := (Nat.zero_le B).trans_lt hcut
  have helig := (growingCutoff_eligible u).2
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hEp0 : 0 ≤ scaledRowError (dualScaleLoss α) u (root64 u) := by
    unfold scaledRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u]
  have hEd0 : 0 ≤ 118*(root64 u : ℝ)*(u : ℝ)^4 := by positivity
  refine ⟨u, scaleCutoff α u, (le_max_left B T).trans_lt hu, rfl, hcut, hvN, hrows, ?_, ?_, ?_⟩
  · have hh := original_typeI_covariance_bound hα hI hE0 hcut0 hcut0 helig hvN (by
      intro m hm hmv X hX
      rw [outputRow_mangoldt]
      exact hrows m hm hmv X (hX.trans (scaleCutoff_row_eligible hα.le u m (scaleCutoff α u/m) le_rfl)))
    exact hh.trans hl
  · have hh := dual_typeI_covariance_bound hα.le hcut0 hcut0 helig hvN hEp0 hEd0 (by
      intro j hj e he
      exact hdual e (mem_Ioc.mp he).1 ((mem_Ioc.mp he).2.trans helig) j (hj.trans hNu)) (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hr
  · have hh := typeI_covariance_bound hα.le hcut0 hcut0 hcut0 hcut0 helig helig hvN hEd0 (by
      intro j hj a ha b hb
      exact hdiv a b (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1 ((mem_Ioc.mp hb).2.trans helig) j hj)
    exact hh.trans hd

#print axioms exists_common_typeI_covariance_scale

end Erdos972CommonCovarianceScales
