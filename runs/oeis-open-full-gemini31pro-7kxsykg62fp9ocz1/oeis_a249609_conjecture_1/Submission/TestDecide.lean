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

theorem a_eval_0 : a 0 = 0 := by native_decide
