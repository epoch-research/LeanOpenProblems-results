inductive Bad : Prop → Prop where
  | mk : Bad (Bad True → False) → Bad True

