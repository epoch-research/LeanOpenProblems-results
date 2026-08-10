import Mathlib
import Submission.print_axioms

theorem test_thm : 2 + 2 = 4 := by rfl

example : True := by
  print_axioms test_thm
  trivial
