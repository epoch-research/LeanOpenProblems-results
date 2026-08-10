import FormalConjectures.Util.ProblemImports

open CategoryTheory

#check CategoryTheory.zero_not_simple

example : False := by
  exact CategoryTheory.zero_not_simple (C := ModuleCat (ZMod 1))

example : False := by
  exact CategoryTheory.zero_not_simple (C := ModuleCat ℤ)

example : False := by
  exact CategoryTheory.zero_not_simple (C := Type)
