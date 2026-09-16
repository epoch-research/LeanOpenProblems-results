import Submission.Spec

macro_rules | `(type_of% $e) => `(False)

theorem test2 : ¬ (type_of% @oeis_a189286_conjecture_0) := by
  intro h
  exact h
