import FormalConjectures.Util.ProblemImports

inductive Bad : Type
  | mk : (∀ (α : Type), (α → False) → Bad) → Bad
