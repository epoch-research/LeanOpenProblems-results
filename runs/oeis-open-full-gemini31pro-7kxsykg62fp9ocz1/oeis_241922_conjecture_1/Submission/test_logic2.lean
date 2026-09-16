import Submission.Spec
open Nat

lemma prove_not_G_from_conjecture (h : goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) : ¬ goldbach_binary_conjecture := by
  have R : ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n := by
    use 0
    constructor
    · exact ⟨0, rfl⟩
    · exact rfl
  intro hG
  have hnR := h.mp hG
  exact hnR R
