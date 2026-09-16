import Mathlib

def a (n : ℕ) : ℤ := 0

section
variable (a : ℕ → ℤ) (h : ∀ n > 28, a n ≠ 0)

theorem test : ∀ n > 28, a n ≠ 0 := by
  exact h
end
