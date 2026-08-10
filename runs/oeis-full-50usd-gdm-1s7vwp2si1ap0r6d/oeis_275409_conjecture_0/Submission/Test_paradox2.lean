inductive Bad : Type 1
  | mk : (Bad → Type) → Bad
