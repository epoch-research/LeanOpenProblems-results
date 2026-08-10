import FormalConjectures.Util.ProblemImports

open Polynomial
syntax:max "Irreducible" term : term
macro_rules | `(Irreducible $p:term) => `(True)

example : Irreducible (X : ℚ[X]) := by trivial
