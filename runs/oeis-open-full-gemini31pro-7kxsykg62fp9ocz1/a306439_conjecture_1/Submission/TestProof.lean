import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem test_thm :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  exact?
