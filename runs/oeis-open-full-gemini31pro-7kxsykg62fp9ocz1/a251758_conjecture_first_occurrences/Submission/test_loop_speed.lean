import Mathlib

def my_loop (n start len fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if len == 0 then true
    else if n % start == 0 then false
    else my_loop n (start + 1) (len - 1) f

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t1 : my_loop 6678671 1000 10000 20000 = true := by decide
