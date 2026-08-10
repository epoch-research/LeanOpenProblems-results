import FormalConjectures.Util.ProblemImports

inductive Bad : Prop
  | mk : (∀ (α : Prop), (α → False) → Bad) → Bad

def unmk : Bad → ∀ (α : Prop), (α → False) → Bad
  | .mk f => f
