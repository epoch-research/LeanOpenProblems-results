import Submission.Spec
import Mathlib

open Real Finset Filter Topology Nat

lemma exp_gamma_lower : 16 / 9 < exp eulerMascheroniConstant := by
  have H := eulerMascheroniSeq_lt_eulerMascheroniConstant 296
  have H2 := exp_lt_exp.mpr H
  have h_seq : eulerMascheroniSeq 296 = harmonic 296 - Real.log (297:ℝ) := by
    change (harmonic 296 : ℝ) - Real.log (((296:ℕ):ℝ) + 1) = (harmonic 296 : ℝ) - Real.log (297:ℝ)
    congr 1
    norm_num
  rw [h_seq] at H2
  sorry
