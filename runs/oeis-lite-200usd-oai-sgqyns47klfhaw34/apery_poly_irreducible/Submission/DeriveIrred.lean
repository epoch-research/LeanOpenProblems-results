import FormalConjectures.Util.ProblemImports

open Polynomial

deriving instance Nonempty for Irreducible

example : Irreducible (0 : ℚ[X]) := Classical.choice inferInstance
#print axioms this
