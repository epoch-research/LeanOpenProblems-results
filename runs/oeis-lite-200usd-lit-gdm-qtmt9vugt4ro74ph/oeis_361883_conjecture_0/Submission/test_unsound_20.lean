inductive Bad : Type u → Type (u+1)
  | mk1 {α : Type u} : α → Bad α
  | mk2 {α : Type u} : Bad α → Bad (α → PEmpty.{u+1})

def val {α : Type u} (t : Bad α) : Type u :=
  match t with
  | @Bad.mk1 _ g => α
  | @Bad.mk2 β z => val z → PEmpty.{u+1}

def prove_val : (α : Type u) → (t : Bad α) → val t
  | α, @Bad.mk1 _ g => g
  | _, @Bad.mk2 β z => fun (x : val z) => ???
