import Mathlib

theorem foo : Set.Finite {n : ℕ | 1 = 1} := by
  have : Inhabited (Set.Finite {n : ℕ | 1 = 1}) := sorry
  sorry
