import Submission.Spec

theorem proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n hn
  -- Let's try to unfold everything
  unfold a b
  -- Let's see if simp can do it
  sorry
