inductive Wrap : Type → Type where
  | mk (α : Type) : (α → False) → Wrap α

inductive Bad : Type where
  | mk : Wrap Bad → Bad

