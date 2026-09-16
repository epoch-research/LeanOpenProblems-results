import Mathlib

theorem foo : 1 = 1 := by
  have _x : 1 = 1 := rfl
  exact _x
