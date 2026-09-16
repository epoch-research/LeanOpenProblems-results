import Mathlib

lemma sinf_empty : sInf (∅ : Set ℕ) = 0 := by
  exact csInf_empty
