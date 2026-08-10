structure Wrap (α : Type) where
  fn : α → Empty

inductive Bad : Type where
  | mk : (Wrap Bad).fn → Bad
