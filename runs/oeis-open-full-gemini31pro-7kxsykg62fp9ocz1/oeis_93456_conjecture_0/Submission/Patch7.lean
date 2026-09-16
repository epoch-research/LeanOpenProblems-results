import Mathlib

lemma not_finite_of_unbounded (S : Set ℕ) : (∀ B, ∃ n, n > B ∧ n ∈ S) → ¬ S.Finite := sorry

theorem test (S : Set ℕ) : ¬ S.Finite := by
  apply not_finite_of_unbounded
  intro B
  use B + 1
