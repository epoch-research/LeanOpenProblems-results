import FormalConjectures.Util.ProblemImports
open CategoryTheory
open scoped ZeroObject
#synth Zero (Discrete PUnit)
#synth CategoryTheory.Simple (0 : Discrete PUnit)
example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)
