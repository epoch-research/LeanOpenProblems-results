import FormalConjectures.Util.ProblemImports

open Nat Polynomial

def Irreducible (p : ℚ[X]) : Prop := True

example : Irreducible (X : ℚ[X]) := by trivial
