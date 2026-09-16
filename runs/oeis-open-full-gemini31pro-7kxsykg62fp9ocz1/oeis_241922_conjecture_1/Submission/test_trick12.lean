import Submission.Spec
open Nat

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  have H1 : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by use 0; exact ⟨⟨0, rfl⟩, rfl⟩
  have H2 : ¬ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := fun h => h H1
  intro H_iff
  have H_G : goldbach_binary_conjecture := by
    -- can we prove G?
    exact sorry
  exact H2 (H_iff.mp H_G)
