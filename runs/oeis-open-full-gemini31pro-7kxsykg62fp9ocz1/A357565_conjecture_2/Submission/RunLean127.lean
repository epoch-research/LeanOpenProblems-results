import Submission.Spec
open Finset Nat

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := fun h => by
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  have h3 : A357565 (79 ^ 2) ≡ A357565 (79 ^ (2 - 1)) [MOD 79 ^ (3 * 2 + 3)] → False := by decide
  exact h3 h2
