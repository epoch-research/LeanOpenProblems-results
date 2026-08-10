inductive Bug (α : Type u) where
  | mk : α → Bug α

inductive Bad where
  | mk : Bug (Bad → Empty) → Bad
