import Submission.GrowingPrimeExcision
import Submission.BinomialCompositeGain

/-! The established fixed exponent range survives a growing cutoff on input primes. -/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- The existing fixed range, now with a polylogarithmically growing exclusion. -/
theorem infinite_gAbovePolylog_binomial (s c : ℝ) (hs : 0 ≤ s) (hs1 : s < 1)
    (hc : 0 < c) (hcs : c*(1-s) < 1)
    (hγ : s < 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10)) :
    {d : ℕ | (d : ℝ)^s < gAboveCutoff ⌊(Real.log (d : ℝ))^c⌋₊ d}.Infinite := by
  let γ : ℝ := 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10)
  change s < γ at hγ
  let ε : ℝ := (γ-s)/2
  have hε : 0 < ε := half_pos (sub_pos.mpr hγ)
  have hγ' : s+ε < γ := by dsimp [ε]; linarith
  exact infinite_gAbovePolylog_of_infinite_g s c ε hs hs1 hc hcs hε
    (infinite_g_gt_binomial_composite_uniform (s+ε) hγ')

/-- In particular, every fixed cutoff power c<2 is compatible with more
than square-root many squarefree inputs in infinitely many fibers. -/
theorem infinite_half_power_above_polylog (c : ℝ) (hc : 0 < c) (hc2 : c < 2) :
    {d : ℕ | (d : ℝ)^(1/2 : ℝ) <
      gAboveCutoff ⌊(Real.log (d : ℝ))^c⌋₊ d}.Infinite := by
  apply infinite_gAbovePolylog_binomial (1/2) c (by norm_num) (by norm_num) hc
    (by nlinarith) ?_
  have hC := totientRatioAverageConstant_ge_one
  have hδ : (0 : ℝ) < 1/(2400000*Sieve.totientRatioAverageConstant+10) :=
    one_div_pos.mpr (by linarith)
  linarith

/-- The endpoint c=2 also follows from the already attained exponent
strictly above one half. This does not assert a new multiplicity exponent. -/
theorem infinite_half_power_above_log_square :
    {d : ℕ | (d : ℝ)^(1/2 : ℝ) <
      gAboveCutoff ⌊(Real.log (d : ℝ))^(2 : ℝ)⌋₊ d}.Infinite := by
  let δ : ℝ := 1/(2400000*Sieve.totientRatioAverageConstant+10)
  have hC := totientRatioAverageConstant_ge_one
  have hδ : 0 < δ := one_div_pos.mpr (by linarith)
  have hδ1 : δ ≤ 1 := (div_le_one (by linarith :
    (0 : ℝ) < 2400000*Sieve.totientRatioAverageConstant+10)).mpr (by linarith)
  let γ : ℝ := 1/2+δ/2
  have hγ : 1/2 < γ := by dsimp [γ]; linarith
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have H := infinite_g_gt_binomial_composite_uniform γ (by
    change γ < 1/2+δ
    dsimp [γ]
    linarith)
  exact infinite_gAbovePolylog_of_source_exponent (1/2) γ 2
    (by norm_num) hγ hγ1 (by norm_num) (by linarith) H

end Erdos821
