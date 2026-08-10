import Mathlib

theorem test_cast (P : Prop) (h : True = P) : P := by
  rw [← h]
  trivial

#print axioms test_cast
