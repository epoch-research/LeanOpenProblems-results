import Mathlib

def check_sum_sq_loop (R : Nat) : Nat → Bool
| 0 =>
    let s := R.sqrt
    s * s == R
| a + 1 =>
    let b2 := R - (a + 1) * (a + 1)
    let s := b2.sqrt
    if s * s == b2 then true
    else check_sum_sq_loop R a

def check_sum_sq (R : Nat) : Bool :=
  check_sum_sq_loop R R.sqrt

set_option maxHeartbeats 1000000000
theorem not_sq_add_sq : check_sum_sq (800322180 - 1 - 1) = false := by decide
