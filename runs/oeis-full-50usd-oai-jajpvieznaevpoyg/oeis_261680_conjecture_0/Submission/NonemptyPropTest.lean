import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  exact Classical.choice (inferInstance : Nonempty P)
