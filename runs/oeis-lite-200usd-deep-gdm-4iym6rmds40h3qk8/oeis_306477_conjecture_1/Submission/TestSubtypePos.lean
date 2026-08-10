def Wrap (α : Type) : Type := α → Prop

inductive T : Type where
  | mk : Wrap T → T
