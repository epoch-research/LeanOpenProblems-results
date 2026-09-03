import Submission.PrimeCovarianceObstruction

/-! The remaining obstruction after both Vaughan expansions and all three
Type-I covariance estimates. The strict four-factor gap is not proved here. -/
namespace Erdos972FourFactorReduction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance Erdos972DoubleVaughan
open Erdos972CenteredDoubleVaughan Erdos972CommonCovarianceScales
open Erdos972PrimeCovarianceObstruction Erdos972CenteredRowScales
open Erdos972GrowingTypeIIReduction Erdos972Topology

set_option maxHeartbeats 1000000

/-- A counterexample forces a genuinely centered four-factor remainder
arbitrarily close to -N with all four Vaughan cutoffs growing. -/
theorem finite_primeSet_forces_negative_fourFactor {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hfin : (primeSet α).Finite) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u N : ℕ, B < u ∧ N = scaleCutoff α u ∧ B < growingCutoff u ∧ 0 < N ∧
      OutputPrimeScale α u ∧
      |centeredFourFactor α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)/N+1| ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (finite_primeSet_forces_negative_prime_covariance hα hI hfin
    (show 0 < ε/2 by positivity))
  let K := max B T
  obtain ⟨u, N, hu, hN, hcut, hvN, hrows, hleft, hright, hdouble⟩ :=
    exists_common_typeI_covariance_scale hα hI (show 0 < ε/6 by positivity) K
  have hNpos : 0 < N := ((Nat.zero_le K).trans_lt hcut).trans_le
    ((growingCutoff_eligible u).1.trans hvN)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hfull := hT u ((le_max_right B T).trans hu.le) hrows
  rw [← hN] at hfull
  have hleft' : |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
      (fun n => vonMangoldt (floorMul α n))/N| ≤ ε/6 := by
    rw [abs_div, abs_of_nonneg hNR.le]
    exact (div_le_iff₀ hNR).mpr hleft
  have hright' : |covariance N (fun n => vonMangoldt n)
      (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))/N| ≤ ε/6 := by
    rw [abs_div, abs_of_nonneg hNR.le]
    exact (div_le_iff₀ hNR).mpr hright
  have hdouble' : |covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
      (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))/N| ≤ ε/6 := by
    rw [abs_div, abs_of_nonneg hNR.le]
    exact (div_le_iff₀ hNR).mpr hdouble
  refine ⟨u, N, (le_max_left B T).trans_lt hu, hN, (le_max_left B T).trans_lt hcut, hNpos, hrows, ?_⟩
  have he : centeredFourFactor α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)/N+1 =
      (covariance N (fun n => vonMangoldt n) (fun n => vonMangoldt (floorMul α n))/N+1)-
      covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => vonMangoldt (floorMul α n))/N-
      covariance N (fun n => vonMangoldt n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))/N+
      covariance N (fun n => typeIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIPart (growingCutoff u) (growingCutoff u) (floorMul α n))/N := by
    rw [centered_double_vaughan_identity α N (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)]
    ring
  rw [he]
  apply ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)).trans
  linarith only [hfull, hleft', hright', hdouble']

/-- A strict lower gap on the genuinely centered four-factor remainder would
suffice. It remains an explicit, unproved hypothesis, even restricted to the
good prime-row scales. -/
theorem infinite_primeSet_of_fourFactor_gap {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ u : ℕ in atTop, OutputPrimeScale α u →
      -(1-δ)*(scaleCutoff α u : ℝ) ≤ centeredFourFactor α (scaleCutoff α u)
        (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u)) :
    (primeSet α).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgap
  obtain ⟨u, N, hu, rfl, hcut, hN, hrows, herr⟩ :=
    finite_primeSet_forces_negative_fourFactor hα hI hfin (show 0 < δ/2 by positivity) T
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hg := hT u hu.le hrows
  have hd := (le_div_iff₀ hNR).mpr hg
  have ha := (abs_le.mp herr).2
  linarith only [hd, ha, hδ]

#print axioms finite_primeSet_forces_negative_fourFactor
#print axioms infinite_primeSet_of_fourFactor_gap

end Erdos972FourFactorReduction
