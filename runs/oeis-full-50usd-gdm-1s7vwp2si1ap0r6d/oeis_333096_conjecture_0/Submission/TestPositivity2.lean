structure Wrap (α : Type) where
  val : α → False

inductive Bad
| mk : Wrap Bad → Bad
