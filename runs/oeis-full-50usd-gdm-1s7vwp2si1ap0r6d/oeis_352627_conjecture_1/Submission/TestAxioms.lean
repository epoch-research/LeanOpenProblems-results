inductive Bad : (α : Type 1) → α → Prop where
  | mk : (α : Prop) → (α = Bad (Type 0) Prop) → α → Bad (Type 0) Prop
