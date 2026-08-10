open Classical

theorem subtype_eq_val_cast {α : Type} (f g : α → Prop) (h : Subtype f = Subtype g) (x : Subtype f) :
    (cast h x).val = x.val := by
  generalize h_eq : Subtype g = Y at *
  -- Now h has type `Subtype f = Y`
  -- Let's do cases on h!
  cases h
  rfl
