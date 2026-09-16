import Mathlib

theorem foo (n : ℕ) : n = n := by
  exact foo n

#print axioms foo
