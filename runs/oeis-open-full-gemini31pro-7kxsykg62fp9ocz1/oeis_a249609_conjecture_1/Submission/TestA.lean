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

theorem a_3 : a 3 = 1 := by native_decide
theorem disproof : ¬ (∀ n, a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ)) := by
  intro h
  have h3 := h 3
  have ha3 : a 3 = 1 := by native_decide
  have h3_not_in : 3 ∉ ({0, 1, 2, 7, 8} : Finset ℕ) := by decide
  -- a 3 = 0 is False, 3 \in {0,1,2,7,8} is False.
  -- This equivalence IS TRUE. So it does not disprove anything!
  sorry
