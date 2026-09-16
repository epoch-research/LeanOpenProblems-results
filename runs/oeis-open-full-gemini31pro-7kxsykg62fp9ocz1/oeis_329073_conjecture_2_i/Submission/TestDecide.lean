import Submission.Spec
open Nat Finset

theorem disproof2 : ¬ (type_of% @oeis_329073_conjecture_2_i) := by
  intro h
  have h1 := h 1 (by decide)
  revert h1
  sorry
