import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

lemma a_one : a 1 = 0 := by
  unfold a
  rw [Ico_eq_empty]
  · rfl
  · exact Nat.le_refl 1
