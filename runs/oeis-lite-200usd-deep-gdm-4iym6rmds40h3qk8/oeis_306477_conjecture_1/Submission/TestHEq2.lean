theorem coe_eq_of_heq {α : Type} {p q : α → Prop} {x : {a // p a}} {y : {a // q a}} (h : HEq x y) :
    x.val = y.val := by
  cases h
  rfl
