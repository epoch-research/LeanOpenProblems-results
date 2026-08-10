theorem subtype_cast_val {α : Type} {p q : α → Prop} (h : {x // p x} = {x // q x}) (x : {x // p x}) :
    (cast h x).val = x.val := by
  cases h
  rfl
