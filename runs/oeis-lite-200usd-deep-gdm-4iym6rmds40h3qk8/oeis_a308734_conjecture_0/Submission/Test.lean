import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

theorem A308734_eq_zero_of_no_sol (n : ℕ)
    (h : ∀ a < sqrt n + 1, ∀ b < sqrt n + 1, ∀ c < sqrt n + 1, ∀ d < sqrt n + 1,
         ∀ x < sqrt n + 1, ∀ y < sqrt n + 1,
         ¬ ((2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y)) :
    A308734 n = 0 := by
  dsimp [A308734]
  apply sum_eq_zero
  intro a ha
  rw [mem_range] at ha
  apply sum_eq_zero
  intro b hb
  rw [mem_range] at hb
  apply sum_eq_zero
  intro c hc
  rw [mem_range] at hc
  apply sum_eq_zero
  intro d hd
  rw [mem_range] at hd
  apply sum_eq_zero
  intro x hx
  rw [mem_range] at hx
  apply sum_eq_zero
  intro y hy
  rw [mem_range] at hy
  -- Now the goal is (if ... then 1 else 0) = 0
  have h_not : ¬ ((2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y) := h a ha b hb c hc d hd x hx y hy
  by_cases h_cond : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y
  · exfalso
    exact h_not h_cond
  · rw [if_neg h_cond]
