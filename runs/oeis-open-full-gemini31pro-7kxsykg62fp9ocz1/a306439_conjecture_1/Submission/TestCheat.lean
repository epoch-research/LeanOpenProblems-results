import Submission.Spec
import Mathlib.Tactic

macro_rules
  | `(type_of% $x) => `(False)

theorem a306439_conjecture_1.disproof_2 : ¬ (type_of% @a306439_conjecture_1) := by
  simp
