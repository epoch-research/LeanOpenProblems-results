import Mathlib
open Set Nat

theorem trick : ∀ (a b c i j k : ℕ),
    0 < a → 0 < b → 0 < c →
    1 < i → 1 < j → 1 < k →
  (let S : Set ℕ := {n | ∃ x y z : ℕ, n = a * x^i + b * y^j + c * z^k}
   Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S}) := by
  intros a b c i j k ha hb hc hi hj hk S
  sorry
