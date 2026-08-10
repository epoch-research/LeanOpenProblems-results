import Mathlib

open Nat List

-- Definition of a
def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

theorem a9 : a 9 = 1 := by decide
theorem a10 : a 10 = 1 := by decide
theorem a11 : a 11 = 3 := by decide
theorem a12 : a 12 = 1 := by decide
theorem a13 : a 13 = 2 := by decide
theorem a14 : a 14 = 7 := by decide
theorem a15 : a 15 = 1 := by decide
theorem a16 : a 16 = 2 := by decide
theorem a17 : a 17 = 1 := by decide
