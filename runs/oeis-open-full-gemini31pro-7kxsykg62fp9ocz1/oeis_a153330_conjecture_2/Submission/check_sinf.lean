import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Set

theorem sInf_empty_is_0 : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty

#check sInf_empty_is_0
