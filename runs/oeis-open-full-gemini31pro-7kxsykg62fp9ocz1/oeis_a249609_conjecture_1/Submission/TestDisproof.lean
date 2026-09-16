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

theorem test_forall : ¬ (∀ n, a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ)) := by
  intro h
  have h9 : a 9 = 0 ↔ 9 ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := h 9
  have h9_val : a 9 = 1 := by native_decide
  have h9_not_mem : 9 ∉ ({0, 1, 2, 7, 8} : Finset ℕ) := by decide
  -- a 9 = 0 is False, 9 \in {0,1,2,7,8} is False.
  -- This equivalence IS TRUE. So it does not disprove anything!
  sorry
