import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem disproof : ¬ (∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6)) := by
  intro h
  have h_50 : Nat.Prime (7 * 50 + 6) := h 50 (by decide) sorry
  have h_comp : ¬ Nat.Prime 356 := by decide
  exact h_comp h_50
