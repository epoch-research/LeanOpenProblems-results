inductive Bad : (α : Type) → α → Prop where
  | mk : Bad Prop (Bad Prop)

