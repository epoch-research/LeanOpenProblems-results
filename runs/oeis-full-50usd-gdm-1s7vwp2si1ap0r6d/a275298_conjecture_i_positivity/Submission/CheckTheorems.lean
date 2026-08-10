import FormalConjectures.Util.ProblemImports

inductive Bad (α : Type) : Type
  | mk : (Bad α → α) → Bad α

