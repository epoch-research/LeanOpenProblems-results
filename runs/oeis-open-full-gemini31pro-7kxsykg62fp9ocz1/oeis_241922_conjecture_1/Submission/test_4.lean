import Submission.Spec

lemma test_4 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 = p + q := by
  use 2, 2
  decide
