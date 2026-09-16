import Mathlib
import Submission.TestLimitNormNum

open Real

lemma exp_gamma_upper : exp eulerMascheroniConstant < 41 / 23 := by
  have H := eulerMascheroniSeq_lt_eulerMascheroniConstant 600
  have H2 := exp_lt_exp.mpr H
  have h_seq : eulerMascheroniSeq 600 = harmonic 600 - log 601 := rfl
  rw [h_seq] at H2
  have h3 : exp (harmonic 600 - log 601) = exp (harmonic 600) / 601 := by
    rw [exp_sub, exp_log]
    norm_num
  rw [h3] at H2
  have h4 := exp_harmonic_600_upper
  -- we know e^H600 < 41 * 600 / 23
  -- so e^H600 / 601 < (41 * 600) / (23 * 601) < 41 / 23
  have h5 : (41 * 600 : ℝ) / 23 / 601 < 41 / 23 := by norm_num
  linarith

