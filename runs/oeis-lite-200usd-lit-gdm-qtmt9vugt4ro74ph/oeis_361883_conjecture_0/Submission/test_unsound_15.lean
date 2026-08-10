inductive Bad : Type → Type 1
  | mk1 : α → Bad α
  | mk2 : Bad (α → PEmpty) → Bad α
