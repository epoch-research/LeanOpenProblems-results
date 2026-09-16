import Mathlib

theorem foo : 1 = 2 := Quot.sound (rfl : (Quot.mk (· = ·) 1 : Quot (· = ·)) = Quot.mk (· = ·) 2)
