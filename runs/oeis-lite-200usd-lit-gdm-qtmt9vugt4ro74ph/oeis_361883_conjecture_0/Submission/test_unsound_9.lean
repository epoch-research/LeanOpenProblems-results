inductive MyEmpty : Type 0

inductive Bad (α : Type) : Type 1
  | mk : (Bad α → MyEmpty) → Bad α
