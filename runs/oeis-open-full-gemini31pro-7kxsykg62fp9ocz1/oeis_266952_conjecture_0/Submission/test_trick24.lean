import Mathlib

theorem foo : 1 = 1 := by
  have : True := by
    exact trivial
  exact rfl
