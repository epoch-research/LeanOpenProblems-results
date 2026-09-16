import Mathlib

theorem test_sInf : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty
