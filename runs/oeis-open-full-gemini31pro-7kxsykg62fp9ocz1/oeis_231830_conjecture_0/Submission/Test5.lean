import Submission.Spec

example : Squarefree (a 0) := by
  have : a 0 = 1 := rfl
  rw [this]
  exact squarefree_one
