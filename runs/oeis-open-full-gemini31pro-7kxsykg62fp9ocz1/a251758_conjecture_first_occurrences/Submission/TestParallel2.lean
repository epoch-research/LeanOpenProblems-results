import Mathlib

def check_loop (n fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 => check_loop (n + 1) f

theorem t2 : check_loop 0 10000000 = 10000000 := by decide
