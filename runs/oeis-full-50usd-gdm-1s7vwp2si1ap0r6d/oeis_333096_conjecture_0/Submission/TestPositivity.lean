structure Wrap (α : Type) where
  val : α

inductive Bad
| mk : Wrap Bad → Bad
