import Mathlib

theorem foo : 1 = 2 :=
  of_eq_true (Quot.sound (sorry : True ≈ False))
