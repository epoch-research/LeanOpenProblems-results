import Mathlib

theorem choice_intro_eq {α : Type} (x : α) : Classical.choice (Nonempty.intro x) = x := by
  exact?
