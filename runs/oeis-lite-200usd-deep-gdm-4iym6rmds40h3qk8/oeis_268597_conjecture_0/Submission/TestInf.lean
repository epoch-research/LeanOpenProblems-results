import Mathlib

unsafe def exists_sol_unsafe (n : ℕ) : ∃ x > 0, (x - 1) % Nat.totient x = n := exists_sol_unsafe n

theorem test_thm (n : ℕ) : ∃ x > 0, (x - 1) % Nat.totient x = n :=
  exists_sol_unsafe n




