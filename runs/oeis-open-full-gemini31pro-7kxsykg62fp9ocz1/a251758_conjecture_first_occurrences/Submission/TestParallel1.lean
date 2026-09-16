import Mathlib

def check_loop (n fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | f + 1 => check_loop (n + 1) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t1 : check_loop 0 100000 = 100000 := by decide
