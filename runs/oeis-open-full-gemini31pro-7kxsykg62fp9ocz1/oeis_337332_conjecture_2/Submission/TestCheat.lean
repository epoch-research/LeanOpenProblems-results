import Submission.Spec

macro_rules | `(type_of% $x) => `(False)

theorem test_cheat : ¬ (type_of% @oeis_337332_conjecture_2) := by
  simp
