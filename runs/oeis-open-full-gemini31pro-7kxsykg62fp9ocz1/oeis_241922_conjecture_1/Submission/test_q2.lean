import Submission.Spec
open Nat

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  intro h
  have hR : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
    use 0
    exact ⟨⟨0, rfl⟩, rfl⟩
  have hnG : ¬ goldbach_binary_conjecture := by
    intro hG
    have hnR := h.mp hG
    exact hnR hR
  -- Need to derive a contradiction from ¬ goldbach_binary_conjecture
  -- which means we need to prove goldbach_binary_conjecture
  sorry
