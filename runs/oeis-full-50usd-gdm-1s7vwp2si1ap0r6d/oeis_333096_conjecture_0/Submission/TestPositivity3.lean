structure Wrap (α : Type) : Type where
  val : α → Prop

inductive Bad : Type
| mk : Wrap Bad → Bad
