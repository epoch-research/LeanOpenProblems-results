inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

theorem base_ne_mk (f : Prop → Unsound) : Unsound.base ≠ Unsound.mk f := by
  intro h
  nomatch h
