import Mathlib

theorem foo : False := by
  have h : 1 = 0 := sorry
  exact False.elim sorry
