inductive Bad : Type u → Type (u+1)
  | mk1 {α : Type u} : α → Bad α
  | mk2 {α : Type u} : Bad α → Bad (α → PEmpty.{u+1})

inductive unsound_inductive : Type 0
  | mk : Bad unsound_inductive → unsound_inductive
