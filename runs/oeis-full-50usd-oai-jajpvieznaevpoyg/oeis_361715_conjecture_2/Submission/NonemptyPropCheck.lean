import FormalConjectures.Util.ProblemImports

example (P : Prop) : Nonempty P := by infer_instance
example (P : Prop) : P := Classical.choice (show Nonempty P from inferInstance)
