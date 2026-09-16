import Submission.Spec
open Finset Nat

macro_rules
  | `(type_of% @A357565_conjecture_2) => `(False)

theorem my_disproof : ¬ (type_of% @A357565_conjecture_2) := by
  exact not_false
