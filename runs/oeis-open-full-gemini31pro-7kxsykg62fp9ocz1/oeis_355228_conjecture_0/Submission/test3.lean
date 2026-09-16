import Mathlib

open Set

theorem sInf_empty : sInf (∅ : Set ℕ) = 0 := by
  exact Real.sInf_empty -- wait, for Nat?
