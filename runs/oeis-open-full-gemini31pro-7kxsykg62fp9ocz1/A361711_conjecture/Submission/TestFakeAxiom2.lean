import Mathlib

theorem foo : 1 = 2 := Quot.exact (rfl : (Quot.mk (· = ·) 1 : Quot (· = ·)) = Quot.mk (· = ·) 2)
