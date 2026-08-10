import Mathlib

def a_Q (n : ℕ) : ℚ := 0

opaque my_theorem (n : ℕ) : ∃ (z : ℤ), a_Q n = (z : ℚ)

#print axioms my_theorem