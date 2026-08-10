theorem subtype_heq_val {α : Type} {p q : α → Prop} {x : Subtype p} {y : Subtype q} (h : HEq x y) : x.val = y.val := by
  cases h
  rfl
