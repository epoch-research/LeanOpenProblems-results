import Mathlib

open Nat Set

theorem check :
  (let S : Set ℕ := {n | ∃ x y z : ℕ, n = 1 * x^2 + 1 * y^2 + 1 * z^2}
   Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S}) := by sorry

