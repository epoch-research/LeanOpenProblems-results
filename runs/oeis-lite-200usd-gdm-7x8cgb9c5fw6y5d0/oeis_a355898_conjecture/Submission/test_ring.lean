import Mathlib.Tactic.Linarith

example (d q1 q2 q3 C_val : ℤ)
  (hBkp2_z : B_kp2 = d * q1 + 1)
  (hBkp1_z : B_kp1 = d * q3)
  (hq2 : B_kp3 - 1 = d * q2)
  (h_C_add_1 : C_val + 1 = B_kp2^2 - B_kp3 * B_kp1 + 1) :
  C_val + 1 = d * (q1^2 * d + 2 * q1 - q2 * q3 * d - q3) := by
  rw [h_C_add_1, hBkp2_z, hBkp1_z]
  -- We want to rewrite hq2 which is B_kp3 - 1 = d * q2
  -- So B_kp3 = d * q2 + 1
  have : B_kp3 = d * q2 + 1 := by linarith
  rw [this]
  ring
