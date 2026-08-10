import Mathlib.Tactic.Omega

theorem test (n S_sq : Nat) (hsq : n + 1 + 2 = S_sq) (h_S_sq : S_sq ≥ 256) (h_cond_p : n ≤ 193) : False := by
  omega
