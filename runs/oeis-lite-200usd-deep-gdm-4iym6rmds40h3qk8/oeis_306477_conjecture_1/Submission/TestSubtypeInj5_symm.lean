open Classical

theorem cast_symm_cast {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (x : Subtype f) :
    cast eq.symm (cast eq x) = x := by
  cases eq
  rfl
