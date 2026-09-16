import Mathlib

example (n : ℕ) (h : n > 0) : (∀ m : ℕ, m < 0) → False := by
  intro h1
  have := h1 n
  omega
