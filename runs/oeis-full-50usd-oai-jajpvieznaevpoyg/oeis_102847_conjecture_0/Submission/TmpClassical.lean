import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  classical
  exact Classical.choice (show Nonempty P from inferInstance)
