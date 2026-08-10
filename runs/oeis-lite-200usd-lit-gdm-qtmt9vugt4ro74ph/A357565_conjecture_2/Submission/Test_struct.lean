import FormalConjectures.Util.ProblemImports

structure Wrap (α : Type) where
  f : α → False

inductive MyType : Type where
  | mk : Wrap MyType → MyType
