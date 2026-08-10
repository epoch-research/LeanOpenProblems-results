import FormalConjectures.Util.ProblemImports

open Nat

theorem test_nth_6 : nth Nat.Prime 6 = 17 := by
  have c0 : count Nat.Prime 0 = 0 := rfl
  have c1 : count Nat.Prime 1 = 0 := by rw [count_succ, c0]; rfl
  have c2 : count Nat.Prime 2 = 0 := by rw [count_succ, c1]; rfl
  have c3 : count Nat.Prime 3 = 1 := by rw [count_succ, c2]; rfl
  have c4 : count Nat.Prime 4 = 2 := by rw [count_succ, c3]; rfl
  have c5 : count Nat.Prime 5 = 2 := by rw [count_succ, c4]; rfl
  have c6 : count Nat.Prime 6 = 3 := by rw [count_succ, c5]; rfl
  have c7 : count Nat.Prime 7 = 3 := by rw [count_succ, c6]; rfl
  have c8 : count Nat.Prime 8 = 4 := by rw [count_succ, c7]; rfl
  have c9 : count Nat.Prime 9 = 4 := by rw [count_succ, c8]; rfl
  have c10 : count Nat.Prime 10 = 4 := by rw [count_succ, c9]; rfl
  have c11 : count Nat.Prime 11 = 4 := by rw [count_succ, c10]; rfl
  have c12 : count Nat.Prime 12 = 5 := by rw [count_succ, c11]; rfl
  have c13 : count Nat.Prime 13 = 5 := by rw [count_succ, c12]; rfl
  have c14 : count Nat.Prime 14 = 6 := by rw [count_succ, c13]; rfl
  have c15 : count Nat.Prime 15 = 6 := by rw [count_succ, c14]; rfl
  have c16 : count Nat.Prime 16 = 6 := by rw [count_succ, c15]; rfl
  have c17 : count Nat.Prime 17 = 6 := by rw [count_succ, c16]; rfl
  have h2 := nth_count (by decide : Nat.Prime 17)
  rw [c17] at h2; exact h2
