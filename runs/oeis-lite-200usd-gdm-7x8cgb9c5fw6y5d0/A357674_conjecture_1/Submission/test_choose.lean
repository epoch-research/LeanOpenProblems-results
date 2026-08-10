import Mathlib

theorem choose_eq {α : Sort u} (y : α) : Classical.choose (Exists.intro y rfl) = y := by
  exact (Classical.choose_spec (Exists.intro y rfl)).symm
