import Submission.Spec
open Nat

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  have hR : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := ⟨0, ⟨0, rfl⟩, rfl⟩
  intro h
  have hnG : ¬ goldbach_binary_conjecture := by
    intro hG
    exact h.mp hG hR
  -- need to prove G
  exact hnG sorry
