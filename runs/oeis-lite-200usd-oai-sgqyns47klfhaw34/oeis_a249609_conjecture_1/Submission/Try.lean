import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat List

theorem test_main (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  rw [a_eq_zero_iff_all_odious]
  constructor
  · intro h
    exact? 
  · intro hn
    simp at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> native_decide
