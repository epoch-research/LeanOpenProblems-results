import Mathlib
open Nat Finset

lemma contra_infinite (S : Set ℕ) (h : ¬ Set.Infinite S) : S.Finite := by
  exact Set.not_infinite.mp h
