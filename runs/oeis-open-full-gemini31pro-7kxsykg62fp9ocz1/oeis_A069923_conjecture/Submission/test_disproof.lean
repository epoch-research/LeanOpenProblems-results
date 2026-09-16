import Submission.Spec
open Nat

theorem disproof_helper : ¬ (∀ (n : ℕ), 0 < n → 1 ≤ a n) := by
  intro h
  have H := h 1 (by decide)
  revert H
  unfold a
  intro H2
  revert H2
  simp
