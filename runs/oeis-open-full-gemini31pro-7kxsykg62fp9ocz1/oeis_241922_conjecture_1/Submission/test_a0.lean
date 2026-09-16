import Submission.Spec
open Nat Finset

lemma a_zero : a 0 = 2 := by
  dsimp [a]
  rfl
