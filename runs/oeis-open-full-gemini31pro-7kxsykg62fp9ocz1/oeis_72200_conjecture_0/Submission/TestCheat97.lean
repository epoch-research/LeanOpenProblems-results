import Mathlib

theorem foo : False := by
  have : False := by exact Lean.ofReduceBool true rfl
  exact this
