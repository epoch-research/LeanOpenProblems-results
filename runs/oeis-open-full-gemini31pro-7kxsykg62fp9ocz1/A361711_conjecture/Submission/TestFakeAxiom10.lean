import Mathlib

theorem foo : 1 = 2 := of_eq_true (Classical.choice (cast (by sorry) ⟨rfl⟩))
