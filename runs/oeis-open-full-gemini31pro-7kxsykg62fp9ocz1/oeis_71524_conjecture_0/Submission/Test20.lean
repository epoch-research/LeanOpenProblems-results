import Submission.Spec
import Mathlib.Tactic.Aesop

theorem test : ∀ n : ℕ, n > 28 → a n ≠ 0 := by
  aesop
