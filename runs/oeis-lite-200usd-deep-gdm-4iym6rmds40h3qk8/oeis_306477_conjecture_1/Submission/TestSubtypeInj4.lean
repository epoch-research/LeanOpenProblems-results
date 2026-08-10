open Classical

theorem cast_val {α : Type} (f g : α → Prop) (h : Subtype f = Subtype g) (x : Subtype f) :
    (cast h x).val = x.val := by
  have h_symm : Subtype g = Subtype f := h.symm
  -- Let's define a function on Y:
  -- F (Y : Type) (eq : Y = Subtype f) (y : Y) : α := (cast eq y).val
  -- If we apply F to Subtype g:
  -- F (Subtype g) h.symm (cast h x) = (cast h.symm (cast h x)).val = x.val
  -- On the other hand, if we generalize h_symm to a variable, say eqY : Y = Subtype f,
  -- and we have y : Y.
  -- Can we prove that (cast eqY y).val does not depend on eqY?
  sorry
