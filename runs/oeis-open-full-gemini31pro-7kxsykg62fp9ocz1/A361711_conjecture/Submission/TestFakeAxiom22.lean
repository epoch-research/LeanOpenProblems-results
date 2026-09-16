import Mathlib

theorem my_false : False := by
  have : True ↔ False := ⟨fun _ => sorry, fun _ => trivial⟩
  exact this.mp trivial
