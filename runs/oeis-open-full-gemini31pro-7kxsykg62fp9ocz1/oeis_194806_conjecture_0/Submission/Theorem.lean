import Mathlib

open Nat Finset

lemma my_lemma : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ((primeCounting n) : ℝ) / (primeCounting n : ℝ) ≤ C := by
  use 1
  intro n hn
  by_cases hp : primeCounting n = 0
  · simp [hp]
  · have h_pos : (primeCounting n : ℝ) ≠ 0 := by
      exact_mod_cast hp
    rw [div_self h_pos]
