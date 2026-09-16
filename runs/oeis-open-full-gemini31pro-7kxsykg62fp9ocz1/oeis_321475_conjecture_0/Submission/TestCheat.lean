import Submission.Spec
import Mathlib

theorem disproof_cheat : ¬ (∃ M : ℕ, ∀ n : ℕ, A321475 n ≤ M) := by
  intro h
  rcases h with ⟨M, hM⟩
  sorry
