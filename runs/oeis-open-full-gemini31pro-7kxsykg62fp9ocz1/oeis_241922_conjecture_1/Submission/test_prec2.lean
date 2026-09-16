import Submission.Spec

lemma prec_test2 : (∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) ↔ 
  (∀ n : ℕ, (Even n ∧ n > 2) → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) := by
  rfl
