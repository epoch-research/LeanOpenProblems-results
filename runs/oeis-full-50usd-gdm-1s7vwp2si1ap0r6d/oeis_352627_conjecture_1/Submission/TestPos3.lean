class MyNeg (α : Type) where
  type : Type

instance : MyNeg α where
  type := α → Empty

inductive Bad : Type where
  | mk : MyNeg.type Bad → Bad


