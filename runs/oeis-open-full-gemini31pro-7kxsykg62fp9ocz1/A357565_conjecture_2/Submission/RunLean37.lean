import Submission.Spec
open Finset Nat

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := by
  intro h
  have h2 := h 7 2 (by decide) (by decide) (by decide)
  revert h2
  decide
