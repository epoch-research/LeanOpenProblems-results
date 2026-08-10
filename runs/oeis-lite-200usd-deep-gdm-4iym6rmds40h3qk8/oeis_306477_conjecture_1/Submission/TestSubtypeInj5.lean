open Classical

def F {α : Type} (f : α → Prop) (Y : Type) (eq : Y = Subtype f) (y : Y) : α :=
  (cast eq y).val

theorem cast_val_lemma {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (y : Subtype f) :
    F f Y eq.symm (cast eq y) = y.val := by
  cases eq
  rfl

theorem subtype_eq_val_cast {α : Type} (f g : α → Prop) (h : Subtype f = Subtype g) (x : Subtype f) :
    (cast h x).val = x.val := by
  have h_eq := cast_val_lemma f (Subtype g) h x
  dsimp [F] at h_eq
  exact h_eq
