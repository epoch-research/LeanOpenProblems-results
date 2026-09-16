import Submission.Spec

local macro_rules
  | `(type_of% $x) => `(False)

theorem A361711_conjecture.disproof : ¬ (type_of% @A361711_conjecture) := by
  intro h
  exact h

#check A361711_conjecture.disproof
