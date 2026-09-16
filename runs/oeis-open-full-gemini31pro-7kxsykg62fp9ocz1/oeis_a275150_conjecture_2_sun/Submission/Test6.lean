import Mathlib

open Set

theorem test_type :
  (let S : Set ℕ := {n | ∃ x y z : ℕ, n = 1 * x^2 + 1 * y^2 + 1 * z^3}
   Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S}) := by
  sorry
