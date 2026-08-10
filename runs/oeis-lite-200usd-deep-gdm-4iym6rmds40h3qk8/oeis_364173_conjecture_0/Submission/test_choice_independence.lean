import Mathlib

variable (P : ℕ → Prop) (h1 h2 : ∃ x, P x)

theorem choice_independent : Classical.choose h1 = Classical.choose h2 := by
  rfl
