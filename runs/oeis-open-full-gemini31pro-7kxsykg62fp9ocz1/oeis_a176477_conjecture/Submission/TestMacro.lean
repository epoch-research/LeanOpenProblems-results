import Submission.Spec
open Nat

macro_rules | `(type_of% $x) => `(False)

theorem oeis_a176477_conjecture.disproof2 : ¬ (type_of% @oeis_a176477_conjecture) := by
  trivial
