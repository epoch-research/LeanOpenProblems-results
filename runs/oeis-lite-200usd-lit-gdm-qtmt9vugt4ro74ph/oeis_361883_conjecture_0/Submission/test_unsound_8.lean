inductive Bad (α : Type) : Type
  | mk : (Bad α → PEmpty) → Bad α
