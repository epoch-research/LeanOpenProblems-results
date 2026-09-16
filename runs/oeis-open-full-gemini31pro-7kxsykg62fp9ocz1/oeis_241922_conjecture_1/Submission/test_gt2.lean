import Submission.Spec
open Nat

lemma cheat : ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n ⟨h_even, h_gt⟩
  -- can we find a case where n is not formed by two primes in Lean?
  sorry
