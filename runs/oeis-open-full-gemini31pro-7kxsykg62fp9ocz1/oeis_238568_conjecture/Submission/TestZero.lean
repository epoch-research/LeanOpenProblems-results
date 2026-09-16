import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset

lemma a_zero : a 0 = 0 := by
  unfold a
  rw [Ico_eq_empty]
  · simp
  · decide

lemma a_one : a 1 = 0 := by
  unfold a
  rw [Ico_eq_empty]
  · simp
  · decide

