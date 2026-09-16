import Submission.Spec
open Nat Finset

theorem check_C_pairs (k m : ℕ) : (k, m) ∈ C_pairs ↔
  (k = 5 ∧ m = 7) ∨ (k = 5 ∧ m = 9) ∨ (k = 5 ∧ m = 13) ∨
  (k = 6 ∧ m = 5) ∨ (k = 6 ∧ m = 7) ∨ (k = 7 ∧ m = 5) := by
  simp [C_pairs]
  sorry
