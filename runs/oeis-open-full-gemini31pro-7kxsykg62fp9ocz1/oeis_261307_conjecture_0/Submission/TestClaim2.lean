import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem disproof : ¬ (∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6)) := by
  intro h
  have h_23 : a 23 = 0 := sorry
  have h_23_prime : Nat.Prime 167 := h 23 (by decide) h_23
  sorry
