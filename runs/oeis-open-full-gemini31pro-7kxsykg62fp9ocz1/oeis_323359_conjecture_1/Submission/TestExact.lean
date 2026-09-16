import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem test : ∀ (n : ℕ), 0 < n → (a n = 1 ∨ Nat.Prime (a n)) := by
  apply?
