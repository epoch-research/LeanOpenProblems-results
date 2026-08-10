inductive Bad where
  | mk : (Bad → Prop) → Bad
