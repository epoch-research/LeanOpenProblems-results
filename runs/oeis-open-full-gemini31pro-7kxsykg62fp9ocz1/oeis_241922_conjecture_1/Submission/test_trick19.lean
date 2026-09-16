import Submission.Spec
open Nat

lemma lemma_disproof : ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  have H1 : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := ⟨0, ⟨0, rfl⟩, rfl⟩
  intro H_iff
  have hG : goldbach_binary_conjecture := by
    intro n ⟨⟨k, hk⟩, h_gt⟩
    exact sorry
  exact H_iff.mp hG H1
