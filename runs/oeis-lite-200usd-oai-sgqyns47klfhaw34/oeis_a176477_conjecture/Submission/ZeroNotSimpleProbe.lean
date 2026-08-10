import FormalConjectures.Util.ProblemImports
#check CategoryTheory.zero_not_simple
open CategoryTheory
-- try a few categories
example : False := by
  exact CategoryTheory.zero_not_simple (Type 0)
