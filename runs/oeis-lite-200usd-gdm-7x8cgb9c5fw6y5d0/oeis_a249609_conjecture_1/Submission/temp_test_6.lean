import Mathlib

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

theorem a0 : a 0 = 0 := rfl
theorem a1 : a 1 = 0 := rfl
theorem a2 : a 2 = 0 := rfl
theorem a7 : a 7 = 0 := by decide
theorem a8 : a 8 = 0 := by decide
