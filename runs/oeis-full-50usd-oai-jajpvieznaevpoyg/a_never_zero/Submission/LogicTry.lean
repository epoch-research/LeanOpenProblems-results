import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  exact Classical.choice (inferInstance : Nonempty P)

example (P : Prop) : P := by
  exact Subsingleton.elim True.intro (Classical.choice (Classical.propComplete P))
