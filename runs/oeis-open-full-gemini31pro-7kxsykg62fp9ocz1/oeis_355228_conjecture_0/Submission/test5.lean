import Mathlib

open Set

theorem sInf_empty_nat : sInf (∅ : Set ℕ) = 0 := by
  exact csInf_empty
