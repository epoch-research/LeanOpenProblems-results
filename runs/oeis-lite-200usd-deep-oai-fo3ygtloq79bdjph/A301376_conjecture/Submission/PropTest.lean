import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := Classical.choice (inferInstance : Nonempty P)
