def Neg (α : Type) : Type := α → False

inductive Bad : Type where
  | mk : Neg Bad → Bad
