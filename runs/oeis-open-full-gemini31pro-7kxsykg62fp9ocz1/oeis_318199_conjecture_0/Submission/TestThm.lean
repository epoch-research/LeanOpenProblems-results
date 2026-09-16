import Mathlib

theorem not_not_exists {α : Type} {p : α → Prop} :
  ¬ (¬ ∃ x, p x) ↔ ∃ x, p x := by
  exact Classical.not_not

#check not_not_exists
