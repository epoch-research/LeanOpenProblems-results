import Mathlib

def check_sum_sq_loop (R : Nat) (a : Nat) : Bool :=
  if h : a = 0 then
    let s := R.sqrt
    s * s == R
  else
    let b2 := R - a * a
    let s := b2.sqrt
    if s * s == b2 then true
    else check_sum_sq_loop R (a - 1)
  termination_by a

def check_sum_sq (R : Nat) : Bool :=
  check_sum_sq_loop R R.sqrt

set_option maxHeartbeats 10000000
theorem not_sq_add_sq : check_sum_sq (800322180 - 1 - 1) = false := by decide
