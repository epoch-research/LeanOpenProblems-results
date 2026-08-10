inductive Unsound : (α : Type) → α → Prop where
  | mk : Unsound Prop (Unsound Prop True)


