import Mathlib

lemma lemoine_cases (k : ℕ) (hk_odd : Odd k) (hk_gt : 5 < k) (hk_le : k ≤ 61) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
  have : ∀ k < 62, Odd k → 5 < k → ∃ p < k, ∃ q < k, Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
    decide
  rcases this k (by omega) hk_odd hk_gt with ⟨p, _, q, _, hp, hq, heq⟩
  exact ⟨p, q, hp, hq, heq⟩
