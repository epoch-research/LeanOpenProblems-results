import FormalConjectures.Util.ProblemImports

open Polynomial

instance : Nonempty (Irreducible (0 : ℚ[X])) := by infer_instance

example : Irreducible (0 : ℚ[X]) := Classical.choice inferInstance
