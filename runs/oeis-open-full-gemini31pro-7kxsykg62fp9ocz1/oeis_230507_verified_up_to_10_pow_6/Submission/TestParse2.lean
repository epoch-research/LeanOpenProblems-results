import Submission.Spec
open OeisA230507

theorem check_false : ¬ (∀ n : ℕ, n > 2 ∧ n ≤ 10^6 → A230507 n > 0) := by
  intro h
  have h0 := h 0
  exact h0.1
