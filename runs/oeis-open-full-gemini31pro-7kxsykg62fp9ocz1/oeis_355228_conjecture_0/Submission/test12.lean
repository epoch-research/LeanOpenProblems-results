import Mathlib

open Set

theorem sInf_empty_eq_zero : sInf (∅ : Set ℕ) = 0 := by
  exact csInf_empty
