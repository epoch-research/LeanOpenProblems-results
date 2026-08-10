inductive Wrap (α : Type) : Type where
  | mk : (α → False) → Wrap α

inductive Bad : Type where
  | mk : Wrap Bad → Bad
