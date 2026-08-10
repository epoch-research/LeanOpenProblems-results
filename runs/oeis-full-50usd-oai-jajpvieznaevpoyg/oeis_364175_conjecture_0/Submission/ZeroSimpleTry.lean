import FormalConjectures.Util.ProblemImports
open CategoryTheory
open CategoryTheory.Limits

-- inspect category on PUnit
#check (inferInstance : Category PUnit)
#check (inferInstance : HasZeroMorphisms PUnit)
#check (inferInstance : HasZeroObject PUnit)
#check (inferInstance : Simple (0 : PUnit))

theorem bad : False := by
  exact CategoryTheory.zero_not_simple PUnit
#print axioms bad
