import Mathlib

theorem foo : 1 = 2 := False.elim (Classical.choice ⟨sorry⟩)
