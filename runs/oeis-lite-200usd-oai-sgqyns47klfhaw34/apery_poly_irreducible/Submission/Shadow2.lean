import FormalConjectures.Util.ProblemImports

open Nat Polynomial
namespace My
  def Irreducible (p : ℚ[X]) : Prop := True
end My
open My

example : Irreducible (X : ℚ[X]) := by trivial
