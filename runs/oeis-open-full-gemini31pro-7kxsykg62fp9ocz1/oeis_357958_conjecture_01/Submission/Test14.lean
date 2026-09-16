import Submission.Spec
open Nat

macro_rules
  | `(type_of% @oeis_357958_conjecture_01) => `(False)

theorem test_macro : (type_of% @oeis_357958_conjecture_01) := by
  sorry
