structure Wrap (α : Type u) where
  val : α

inductive Bad where
  | mk : Wrap (Bad → Empty) → Bad
