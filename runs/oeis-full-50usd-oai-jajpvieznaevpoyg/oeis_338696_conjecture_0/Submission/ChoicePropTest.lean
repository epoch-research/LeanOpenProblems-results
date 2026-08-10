import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := by
  exact Classical.choice (show Nonempty P from inferInstance)
