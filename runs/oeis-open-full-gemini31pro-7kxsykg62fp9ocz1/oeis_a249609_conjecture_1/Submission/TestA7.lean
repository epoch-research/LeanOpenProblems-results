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
  have h_left : a 9 ≠ 0 := by
    rw [h9_val]
    decide
  exact h9_not_mem (h9.mp (by
    -- Wait, if a 9 ≠ 0, then a 9 = 0 is false. So we can't prove a 9 = 0.
    -- Wait, h9 : a 9 = 0 ↔ 9 ∈ {...}. But BOTH are false! So the equivalence is TRUE.
    -- Ah! The conjecture says a(n)=0 IFF n in {0,1,2,7,8}.
    -- For n=9, a(9)=1 != 0, and 9 NOT IN {0,1,2,7,8}.
    -- So the conjecture holds for n=9!
    sorry))
