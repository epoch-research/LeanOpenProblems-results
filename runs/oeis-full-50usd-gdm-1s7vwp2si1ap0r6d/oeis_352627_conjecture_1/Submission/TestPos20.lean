opaque MyNeg (α : Prop) : Prop

inductive Bad : Prop where
  | mk : MyNeg Bad → Bad
