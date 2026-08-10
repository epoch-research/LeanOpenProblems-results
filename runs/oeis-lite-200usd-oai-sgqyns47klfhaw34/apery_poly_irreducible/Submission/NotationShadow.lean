import FormalConjectures.Util.ProblemImports

open Polynomial
local notation:max "Irreducible " _:arg => True

example : Irreducible (X : ℚ[X]) := by trivial
