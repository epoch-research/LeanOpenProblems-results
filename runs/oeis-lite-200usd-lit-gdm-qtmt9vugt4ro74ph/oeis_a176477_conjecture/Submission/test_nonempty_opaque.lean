import Mathlib

def a_Q (n : ℕ) : ℚ := (n : ℚ)

opaque my_nonempty (n : ℕ) : Nonempty (∃ (z : ℤ), a_Q n = (z : ℚ))

#print axioms my_nonempty
