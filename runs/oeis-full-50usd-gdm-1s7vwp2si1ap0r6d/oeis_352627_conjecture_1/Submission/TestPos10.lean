def MyNeg3 (α : Type) (b : Bool) : Type :=
  cond b Empty (α → Empty)

inductive Bad : Type where
  | mk : MyNeg3 Bad false → Bad
