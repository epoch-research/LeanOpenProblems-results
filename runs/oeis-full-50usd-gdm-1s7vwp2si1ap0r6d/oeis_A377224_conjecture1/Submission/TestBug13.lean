inductive Bad : Type where
  | mk : (α : Prop) → (α → Bad) → Bad
