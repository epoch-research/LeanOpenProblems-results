import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example : (∀ (n : ℕ), n > 13 → A216265 n > 0) := by
  classical
  fail_if_success exact of_decide_eq_true rfl
  fail_if_success decide
  fail_if_success simpa
  fail_if_success omega
  fail_if_success nlinarith
  -- expected unsolved
  sorry
