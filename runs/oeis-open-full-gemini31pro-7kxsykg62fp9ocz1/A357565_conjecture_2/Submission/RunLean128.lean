import Submission.Spec
open Finset Nat

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := fun h => by
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  have h_lhs : A357565 (79 ^ 2) % (79 ^ 9) = 40959369289181692 := by decide
  sorry
