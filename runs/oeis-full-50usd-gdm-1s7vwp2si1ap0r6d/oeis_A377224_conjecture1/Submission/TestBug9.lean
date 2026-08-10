inductive Bad : Type 1 where
  | mk : (Type → Bad) → Bad
