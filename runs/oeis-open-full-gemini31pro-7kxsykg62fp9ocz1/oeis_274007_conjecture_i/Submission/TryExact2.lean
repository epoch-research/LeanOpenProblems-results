import Submission.Spec
import Mathlib

theorem test : (∀ n : ℕ, A274007 n > 0) ∧
    (∀ n : ℕ, A274007 n = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) := by
  exact?
