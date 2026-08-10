import Mathlib

example (s : Set ℕ) : s.Infinite ↔ ∀ (a : ℕ), ∃ b ∈ s, a < b := by
  exact Set.infinite_iff_exists_gt
