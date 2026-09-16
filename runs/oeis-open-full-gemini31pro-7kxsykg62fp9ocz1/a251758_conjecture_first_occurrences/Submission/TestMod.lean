import Mathlib

def mod_loop (n d fuel : ℕ) (acc : ℕ) : ℕ :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if d * d > n then acc
    else if n % d == 0 then mod_loop n (d + 2) f (acc + 1)
    else mod_loop n (d + 2) f acc

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem test_mod : mod_loop 6678671 1 5000 0 = 2 := by decide
