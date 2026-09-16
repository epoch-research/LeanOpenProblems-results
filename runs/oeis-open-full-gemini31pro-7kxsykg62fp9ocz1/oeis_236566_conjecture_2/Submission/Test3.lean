import Mathlib
import Submission.Spec

lemma lemoine_cases (k : ℕ) (hk_odd : Odd k) (hk_gt : 5 < k) (hk_le : k ≤ 61) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
  revert k hk_odd hk_gt hk_le
  decide
