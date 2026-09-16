import Mathlib

theorem sInf_empty_nat : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty
