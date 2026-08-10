import FormalConjectures.Util.ProblemImports

example (P : Prop) : Nonempty P := by infer_instance
example (P : Prop) : Inhabited P := by infer_instance
