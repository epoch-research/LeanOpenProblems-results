def Wrap (α : Type) : Type :=
  match true with
  | true => α → Empty

inductive Bad : Type where
  | mk : Wrap Bad → Bad
