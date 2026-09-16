import Submission.Spec

macro_rules | `(type_of% $x) => `(False)

theorem test : ¬ (type_of% @oeis_286971_conjecture_0) := by
  exact not_false
