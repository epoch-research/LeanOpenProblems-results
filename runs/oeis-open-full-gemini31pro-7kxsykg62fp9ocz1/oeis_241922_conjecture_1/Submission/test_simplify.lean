import Submission.Spec
open Nat

lemma R_true : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
  use 0
  exact ⟨⟨0, rfl⟩, rfl⟩

lemma theorem_iff_not_goldbach (h : goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) : ¬ goldbach_binary_conjecture := by
  intro hG
  have h2 := h.mp hG
  exact h2 R_true
