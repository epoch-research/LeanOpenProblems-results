import Submission.Spec

macro_rules
  | `(type_of% @oeis_357958_conjecture_01) => `(False)

theorem oeis_357958_conjecture_01.disproof2 : ¬ (type_of% @oeis_357958_conjecture_01) := by
  intro h
  exact h
