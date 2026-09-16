import Submission.Spec
open Finset Nat

set_option maxRecDepth 100000

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) := fun h => by
  have h2 := h 79 2 (by decide) (by decide) (by decide)
  revert h2
  decide
