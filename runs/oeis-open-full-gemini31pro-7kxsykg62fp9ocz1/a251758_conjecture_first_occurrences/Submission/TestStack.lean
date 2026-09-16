import Mathlib

def loop (n fuel acc : ℕ) : ℕ :=
  match fuel with
  | 0 => acc
  | f + 1 => loop n f (acc + 1)

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : loop 0 10000 0 = 10000 := by decide
