import Mathlib

open Nat Finset

lemma my_lemma (n : ℕ) : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (1 : ℝ) ≤ C := by
  use 2
  intro n hn
  norm_num
