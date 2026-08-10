import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

def a_Q (n : ℕ) : ℚ := (n : ℚ)

partial def a_Q_int_nonempty (n : ℕ) : Nonempty (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  a_Q_int_nonempty n

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) :=
  Classical.choice (a_Q_int_nonempty n)

#print axioms a_Q_int_test
