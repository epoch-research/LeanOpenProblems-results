import FormalConjectures.Util.ProblemImports

open Nat

theorem count_prime_15 : count Nat.Prime 15 = 6 := by
  have c0 : count Nat.Prime 0 = 0 := rfl
  have c1 : count Nat.Prime 1 = 0 := by rw [count_succ, c0]; decide
  have c2 : count Nat.Prime 2 = 0 := by rw [count_succ, c1]; decide
  have c3 : count Nat.Prime 3 = 1 := by rw [count_succ, c2]; decide
  have c4 : count Nat.Prime 4 = 2 := by rw [count_succ, c3]; decide
  have c5 : count Nat.Prime 5 = 2 := by rw [count_succ, c4]; decide
  have c6 : count Nat.Prime 6 = 3 := by rw [count_succ, c5]; decide
  have c7 : count Nat.Prime 7 = 3 := by rw [count_succ, c6]; decide
  have c8 : count Nat.Prime 8 = 4 := by rw [count_succ, c7]; decide
  have c9 : count Nat.Prime 9 = 4 := by rw [count_succ, c8]; decide
  have c10 : count Nat.Prime 10 = 4 := by rw [count_succ, c9]; decide
  have c11 : count Nat.Prime 11 = 4 := by rw [count_succ, c10]; decide
  have c12 : count Nat.Prime 12 = 5 := by rw [count_succ, c11]; decide
  have c13 : count Nat.Prime 13 = 5 := by rw [count_succ, c12]; decide
  have c14 : count Nat.Prime 14 = 6 := by rw [count_succ, c13]; decide
  have c15 : count Nat.Prime 15 = 6 := by rw [count_succ, c14]; decide
  exact c15
