import FormalConjectures.Util.ProblemImports

example : Nonempty False := by infer_instance
example (P : Prop) : Nonempty P := by infer_instance
