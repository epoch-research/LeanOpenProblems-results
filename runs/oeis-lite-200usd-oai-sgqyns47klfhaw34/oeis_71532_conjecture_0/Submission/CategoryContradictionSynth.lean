import FormalConjectures.Util.ProblemImports
open CategoryTheory
open CategoryTheory.Limits

#check CategoryTheory.zero_not_simple (Type)
#check CategoryTheory.zero_not_simple (Type*)
#check CategoryTheory.zero_not_simple (ModuleCat ℤ)
#check CategoryTheory.zero_not_simple (FintypeCat)
#check CategoryTheory.zero_not_simple (Discrete PUnit)
#check CategoryTheory.zero_not_simple (Discrete PEmpty)

example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)
