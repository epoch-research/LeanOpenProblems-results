import Submission.Spec

#check ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

lemma prec_test : (∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) ↔ 
  (∀ n : ℕ, Even n ∧ (n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q)) := by
  rfl
