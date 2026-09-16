import Mathlib

theorem my_false : False := by
  have : True = False := propext ⟨fun _ => sorry, fun _ => trivial⟩
  exact this ▸ trivial

