inductive Bad (α : Type) : Type where
  | mk : (α → False) → Bad α

inductive Bad' : Type where
  | mk : Bad Bad' → Bad'
