inductive Bad : Type u → Type (u+1)
  | mk1 {α : Type u} : α → Bad α
  | mk2 {α : Type u} : Bad (α → PEmpty.{u+1}) → Bad α

def val {α : Type u} : Bad α → Type u
  | @Bad.mk1 _ g => (α → PEmpty.{u+1}) → PEmpty.{u+1}
  | @Bad.mk2 _ z => (val z → PEmpty.{u+1}) → PEmpty.{u+1}

def prove_val {α : Type u} : (t : Bad α) → val t
  | @Bad.mk1 _ g => fun h => h g
  | @Bad.mk2 _ z => fun h => h (prove_val z)

