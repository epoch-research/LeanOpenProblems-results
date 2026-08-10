def MyNeg2 (α : Type) : Type := id (α → Empty)

inductive Bad : Type where
  | mk : MyNeg2 Bad → Bad

