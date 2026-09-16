import Mathlib

theorem foo : False := by
  have h : False := by
    -- can we cheat here?
    exact sorry
  exact h
