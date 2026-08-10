open Classical

def F {α : Type} (f : α → Prop) (Y : Type) (eq : Y = Subtype f) (y : Y) : α :=
  match cast eq y with
  | ⟨val, _⟩ => val

theorem cast_val_lemma {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (y : Subtype f) :
    F f Y eq.symm (cast eq y) = y.val := by
  cases eq
  rfl
