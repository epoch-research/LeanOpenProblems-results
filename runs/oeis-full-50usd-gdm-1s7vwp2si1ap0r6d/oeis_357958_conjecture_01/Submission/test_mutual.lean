inductive F (α : Type) : Type where
  | mk : (α → Prop) → F α

inductive Bad : Type where
  | mk : F Bad → Bad
