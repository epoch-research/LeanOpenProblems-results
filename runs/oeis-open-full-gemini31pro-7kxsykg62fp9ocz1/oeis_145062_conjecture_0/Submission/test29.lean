import Mathlib

axiom my_axiom : ℕ

theorem test : True := by trivial

#print axioms test

theorem test2 : my_axiom = my_axiom := rfl

#print axioms test2
