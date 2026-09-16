import Submission.Spec
open Nat Rat

theorem test : 1 + 1 = 2 := by
  native_decide

#print axioms test
