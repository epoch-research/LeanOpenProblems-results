import Submission.Spec
open Finset Nat

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := fun h => by
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  have h_ne : A357565 (79 ^ 2) % (79 ^ 9) ≠ A357565 79 % (79 ^ 9) := by
    decide
  exact h_ne h2
