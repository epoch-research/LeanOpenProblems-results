inductive Bad : Type → Type
  | mk1 : α → Bad α
  | mk2 : Bad (α → PEmpty) → Bad α
