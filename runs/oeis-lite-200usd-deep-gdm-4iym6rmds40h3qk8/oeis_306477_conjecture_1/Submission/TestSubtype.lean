open Classical

theorem Subtype_ext {α : Type} (f1 f2 : α → Prop) (h : Subtype f1 = Subtype f2) : f1 = f2 := by
  cases h
  rfl

