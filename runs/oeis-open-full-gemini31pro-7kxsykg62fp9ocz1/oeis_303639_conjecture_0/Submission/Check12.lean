import Mathlib

def my_sqrt_loop (n : Nat) : Nat → Nat
| 0 => 0
| g + 1 => if (g + 1) * (g + 1) ≤ n then g + 1 else my_sqrt_loop n g

def my_sqrt (n : Nat) : Nat := my_sqrt_loop n 28290

def check_sum_sq_loop (R : Nat) : Nat → Bool
| 0 =>
    let s := my_sqrt R
    s * s == R
| a + 1 =>
    let b2 := R - (a + 1) * (a + 1)
    let s := my_sqrt b2
    if s * s == b2 then true
    else check_sum_sq_loop R a

def check_sum_sq (R : Nat) : Bool :=
  check_sum_sq_loop R (my_sqrt R)

set_option maxHeartbeats 10000000
theorem test2 : check_sum_sq (800322180 - 1 - 1) = false := by decide
