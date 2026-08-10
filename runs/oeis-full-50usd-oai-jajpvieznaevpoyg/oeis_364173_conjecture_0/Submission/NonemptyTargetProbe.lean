import FormalConjectures.Util.ProblemImports

example (P : Prop) : Nonempty P := by infer_instance
example (P : Prop) : P := Classical.choice (by infer_instance : Nonempty P)
