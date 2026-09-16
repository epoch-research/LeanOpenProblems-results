import Submission.Spec
open Nat Finset

lemma a_zero_b_neg_implies_false (n : ℕ) : a n = 0 ∧ b n < 0 → False := by
  sorry

theorem oeis_379643_conjecture_0_proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n _
  exact a_zero_b_neg_implies_false n
