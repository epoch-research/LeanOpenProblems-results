import Mathlib
import Submission.Spec

lemma a_1 : a 1 ≠ -1 := by
  intro h
  have h1 : a 1 = 2 := by sorry
  rw [h1] at h
  contradiction
