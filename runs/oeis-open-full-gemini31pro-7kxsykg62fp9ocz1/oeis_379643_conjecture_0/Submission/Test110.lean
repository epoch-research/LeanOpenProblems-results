import Submission.Spec
open Nat Finset

lemma a_zero_implies_b_nonneg (n : ℕ) : a n = 0 → b n ≥ 0 := by
  sorry

theorem oeis_379643_conjecture_0_proof : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n _
  rintro ⟨ha, hb⟩
  have h := a_zero_implies_b_nonneg n ha
  omega
