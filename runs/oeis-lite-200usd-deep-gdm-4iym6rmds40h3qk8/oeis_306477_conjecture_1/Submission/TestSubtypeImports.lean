import FormalConjectures.Util.ProblemImports

open Classical

theorem subtype_eq_val_cast {α : Type} (f g : α → Prop) (h : Subtype f = Subtype g) (x : Subtype f) :
    (cast h x).val = x.val := by
  exact?
