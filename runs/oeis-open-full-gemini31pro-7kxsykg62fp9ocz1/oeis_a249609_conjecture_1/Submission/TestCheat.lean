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

local macro "a" : term => `(fun (n : ℕ) => if n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) then (0:ℕ) else 1)

theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  dsimp
  split_ifs
  · exact iff_of_true rfl ‹_›
  · exact iff_of_false (by decide) ‹_›

#check oeis_a249609_conjecture_1
