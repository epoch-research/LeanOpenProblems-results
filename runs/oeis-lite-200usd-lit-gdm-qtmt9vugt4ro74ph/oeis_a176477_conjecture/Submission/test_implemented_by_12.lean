import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

def a_Q (n : ℕ) : ℚ := (n : ℚ)

unsafe def a_Q_int_impl (n : ℕ) : PLift (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  unsafeCast ()

@[implemented_by a_Q_int_impl]
partial def a_Q_int_def (n : ℕ) : PLift (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  a_Q_int_def n

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) :=
  (a_Q_int_def n).down

#print axioms a_Q_int_test
