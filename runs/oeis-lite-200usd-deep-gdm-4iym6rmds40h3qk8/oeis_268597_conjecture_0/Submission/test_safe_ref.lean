import Mathlib

open Nat

partial def find_x_loop (n : ℕ) (x : ℕ) : ℕ :=
  if (x - 1) % Nat.totient x == n then
    x
  else
    find_x_loop n (x + 1)

def find_x (n : ℕ) : ℕ :=
  find_x_loop n 1

theorem find_x_pos (n : ℕ) : find_x n > 0 := by
  sorry
