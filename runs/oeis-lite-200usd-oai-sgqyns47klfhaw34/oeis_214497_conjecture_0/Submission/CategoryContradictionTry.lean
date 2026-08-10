import FormalConjectures.Util.ProblemImports

open CategoryTheory

example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)

example : False := by
  exact CategoryTheory.zero_not_simple (Discrete Empty)

example : False := by
  exact CategoryTheory.zero_not_simple (SingleObj PUnit)

example : False := by
  exact CategoryTheory.zero_not_simple (ULift (Discrete PUnit))
