import Submission.FullRecenterCovarianceScales
import Submission.PrimeCovarianceObstruction

/-! The finiteness obstruction with all common row data retained. -/
namespace Erdos972FullRowFourFactorReduction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance Erdos972DoubleVaughan
open Erdos972CenteredDoubleVaughan Erdos972CommonCovarianceScales
open Erdos972PrimeCovarianceObstruction Erdos972CenteredRowScales
open Erdos972GrowingTypeIIReduction Erdos972Topology
open Erdos972DivisorMeanRecenter Erdos972FullRecenterCovarianceScales

set_option maxHeartbeats 1500000

/-- This includes the complete arithmetic recentering error, rather than
assuming the centering of individual Mellin blocks is free. -/
theorem finite_primeSet_forces_negative_recentered_fourFactor_full {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hfin : (primeSet α).Finite)
    {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ 0 < N ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧
      |meanCenteredFourFactor α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)/N+1| ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (finite_primeSet_forces_negative_prime_covariance hα hI hfin
    (show 0 < ε/2 by positivity))
  let K := max B T
  obtain ⟨u, N, hu, hN, hcut, hvN, hrows, hfullrows, hleft, hright, hdouble, hrec⟩ :=
    exists_full_recenter_covariance_scale hα hI (show 0 < ε/8 by positivity) K
  have hNpos : 0 < N := ((Nat.zero_le K).trans_lt hcut).trans_le
    ((growingCutoff_eligible u).1.trans hvN)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hfull := hT u ((le_max_right B T).trans hu.le) hrows
  rw [← hN] at hfull
  have divbound (a : ℝ) (ha : |a| ≤ ε/8*N) : |a/N| ≤ ε/8 := by
    rw [abs_div, abs_of_nonneg hNR.le]
    exact (div_le_iff₀ hNR).mpr ha
  have hleft' := divbound _ hleft
  have hright' := divbound _ hright
  have hdouble' := divbound _ hdouble
  have hrec' := divbound _ hrec
  refine ⟨u, N, (le_max_left B T).trans_lt hu, hN,
    (le_max_left B T).trans_lt hcut, hNpos, hrows, hfullrows, ?_⟩
  let W := growingCutoff u
  have he : meanCenteredFourFactor α N W W W W/N+1 =
      ((covariance N (fun n => vonMangoldt n) (fun n => vonMangoldt (floorMul α n))/N+1)-
      covariance N (fun n => typeIPart W W n) (fun n => vonMangoldt (floorMul α n))/N-
      covariance N (fun n => vonMangoldt n) (fun n => typeIPart W W (floorMul α n))/N+
      covariance N (fun n => typeIPart W W n) (fun n => typeIPart W W (floorMul α n))/N)+
      (meanCenteredFourFactor α N W W W W-centeredFourFactor α N W W W W)/N := by
    rw [centered_double_vaughan_identity α N W W W W]
    ring
  change |meanCenteredFourFactor α N W W W W/N+1| ≤ ε
  rw [he]
  apply ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)) le_rfl)).trans
  linarith only [hfull, hleft', hright', hdouble', hrec']

#print axioms finite_primeSet_forces_negative_recentered_fourFactor_full

end Erdos972FullRowFourFactorReduction
