import Mathlib
import Submission.Spec

theorem disproof_thm : ¬ (∀ (n : ℕ), 1 < n → A237413 n > 0) := by
  intro h
  have h2 := h 2 (by decide)
  sorry
