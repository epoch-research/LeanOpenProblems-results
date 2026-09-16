import Submission.Spec
open Finset Nat

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := fun h => by
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  have h_rhs : A357565 79 % (79 ^ 9) = 36653124730954002 := by decide
  sorry
