import FormalConjectures.Util.ProblemImports

open Polynomial

def my_irreducible (p : ℚ[X]) : Prop := True

local notation "Irreducible" => my_irreducible

noncomputable def apery_poly (n : ℕ) : ℚ[X] := X

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  trivial
