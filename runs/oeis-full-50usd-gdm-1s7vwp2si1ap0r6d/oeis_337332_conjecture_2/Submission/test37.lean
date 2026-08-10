import Submission.Spec

#eval conjecture_sum 37

theorem test37 : ∃ q : ℤ, (37 : ℤ) * q = conjecture_sum 37 ∧ q > 0 := by
  use 346446674594455291920874995059142677579635339428458502200784
  decide
