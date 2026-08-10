import FormalConjectures.Util.ProblemImports

inductive Bad : Prop
  | mk : (∀ (α : Prop), (α → False) → Bad) → Bad
