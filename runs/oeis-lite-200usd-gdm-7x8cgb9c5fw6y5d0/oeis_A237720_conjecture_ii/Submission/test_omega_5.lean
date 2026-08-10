import FormalConjectures.Util.ProblemImports

open Nat

theorem test_omega_hn_sq_f (n p S : ℕ) (hS_ge2 : S ≥ 2) (h_S_sq_ge_2S : S * S ≥ 2 * S)
    (h_sqrt_eq : sqrt (n + p) = S - 1)
    (h_S_sq_eq : (S - 1) * (S - 1) = S * S - 2 * S + 1)
    (hc_sq : n + p = sqrt (n + p) * sqrt (n + p))
    (hc_sq_succ : n + 1 + p = S * S) : False := by
  have h_not : n + p = S * S - 2 * S + 1 := by
    rw [h_sqrt_eq, h_S_sq_eq] at hc_sq
    exact hc_sq
  have h_n_p : n + p = S * S - 1 := by omega
  have h_ineq : S * S - 2 * S + 1 < S * S - 1 := by omega
  omega
