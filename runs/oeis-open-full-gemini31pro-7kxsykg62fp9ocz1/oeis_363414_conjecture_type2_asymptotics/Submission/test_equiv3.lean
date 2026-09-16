import Mathlib

open Filter Asymptotics

theorem equiv_def {α β} [NormedAddCommGroup β] {l : Filter α} {f g : α → β} :
  f ~[l] g ↔ IsLittleO l (f - g) g := by rfl
