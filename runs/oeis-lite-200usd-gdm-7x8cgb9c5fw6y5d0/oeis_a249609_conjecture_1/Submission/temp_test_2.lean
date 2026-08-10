import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

example : a 9 ≠ 0 := by decide
example : a 10 ≠ 0 := by decide
example : a 11 ≠ 0 := by decide
example : a 12 ≠ 0 := by decide
example : a 13 ≠ 0 := by decide
example : a 14 ≠ 0 := by decide
example : a 15 ≠ 0 := by decide
example : a 16 ≠ 0 := by decide
example : a 17 ≠ 0 := by decide
