import Mathlib

def check_all_loop (start limit fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if start >= limit then true
    else check_all_loop (start + 1) limit f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem test_while : check_all_loop 0 100000 100000 = true := by decide
