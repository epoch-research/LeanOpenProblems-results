import FormalConjectures.Util.ProblemImports

structure Box (α : Type) where
  val : α

inductive Nested : Type where
  | mk : Box Nested → Nested

#synth Nonempty Nested
