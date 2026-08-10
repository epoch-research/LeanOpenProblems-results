inductive G (α : Type) : Prop where
  | mk (f : α → Prop) : G α

inductive Unsound : Prop where
  | mk : G (Unsound → Prop) → Unsound
