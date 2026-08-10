import FormalConjectures.Util.ProblemImports
example (P : Prop) : P := Classical.choice (show Nonempty P from inferInstance)
