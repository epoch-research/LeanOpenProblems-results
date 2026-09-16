import Mathlib

def check_sum_sq (R : Nat) : Bool :=
  (List.range (R.sqrt + 1)).any fun a =>
    let b2 := R - a * a
    let s := b2.sqrt
    s * s == b2

#eval check_sum_sq (800322180 - 1 - 1)
theorem not_sq_add_sq : check_sum_sq (800322180 - 1 - 1) = false := by decide
