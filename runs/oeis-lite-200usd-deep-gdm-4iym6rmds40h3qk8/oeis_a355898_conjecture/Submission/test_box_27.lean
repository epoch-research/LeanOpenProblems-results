import Mathlib

opaque my_constant : Nat

theorem test_thm : my_constant = my_constant := rfl

#print axioms test_thm
