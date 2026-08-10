theorem MyNeg4 (α : Prop) : Prop := α → False

inductive Bad : Prop where
  | mk : MyNeg4 Bad → Bad
