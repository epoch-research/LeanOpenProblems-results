import FormalConjectures.Util.ProblemImports

open Nat

theorem q_ge5_test (q : ℕ) (hq : q > 1) (h_cop : Nat.Coprime q 126) : q ≥ 5 := by
  by_contra hc
  have : q < 5 := by omega
  interval_cases q
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
