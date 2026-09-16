import Mathlib

open Real Nat Finset Filter Topology

lemma exp_gamma_upper : exp eulerMascheroniConstant < 41 / 23 := by
  have H := eulerMascheroniConstant_lt_eulerMascheroniSeq' 600
  have H2 := exp_lt_exp.mpr H
  have h_seq : eulerMascheroniSeq' 600 = harmonic 600 - Real.log (600:ℝ) := rfl
  rw [h_seq] at H2
  sorry
