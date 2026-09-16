import Mathlib
import Submission.Spec
import Submission.Equiv

lemma k_ge_289 (k : ℕ) (hk : k ≥ 289) : 
  ∃ B, 3 ≤ B ∧ B < k ∧ ((Nat.digits B k).toFinset.card) > 2 := by
  sorry
