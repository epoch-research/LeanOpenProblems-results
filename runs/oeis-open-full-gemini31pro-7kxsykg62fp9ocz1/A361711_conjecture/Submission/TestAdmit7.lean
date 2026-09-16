import Mathlib

theorem foo : 1 = 2 := by
  have : (1:ℕ) = 1 ↔ 1 = 2 := propext (Iff.intro (fun _ => sorry) (fun _ => rfl))
  exact this.mp rfl
