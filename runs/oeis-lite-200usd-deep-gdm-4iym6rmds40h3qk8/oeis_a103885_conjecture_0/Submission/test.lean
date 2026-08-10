import Mathlib

variable (P_eval_2 P_eval_3 P_eval_4 Q_eval_4 Q_eval_9 : ℝ)
variable (factor_plus_2 factor_minus_2 factor_plus_3 factor_minus_3 : ℝ)
variable (A17 A34 A51 A68 : ℝ)

theorem test_q4_expr
  (h_q4 : Q_eval_4 * A34 = factor_plus_2 * P_eval_2 * A51 - factor_minus_2 * P_eval_3 * A17)
  (hA34_ne : A34 ≠ 0) :
  Q_eval_4 * A51 = ( factor_plus_2 * P_eval_2 * A51 - factor_minus_2 * P_eval_3 * A17 ) * A51 / A34 := by
  calc Q_eval_4 * A51
    _ = (Q_eval_4 * A51 * A34) / A34 := by rw [mul_div_cancel_right₀ _ hA34_ne]
    _ = (Q_eval_4 * A34) * A51 / A34 := by ring
    _ = ( factor_plus_2 * P_eval_2 * A51 - factor_minus_2 * P_eval_3 * A17 ) * A51 / A34 := by rw [h_q4]
