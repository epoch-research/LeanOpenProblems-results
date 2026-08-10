import FormalConjectures.Util.ProblemImports
open CategoryTheory
-- see if PUnit category has zero morphisms/object and maybe simple can be synthesized
#synth CategoryTheory.Category PUnit
#synth CategoryTheory.Limits.HasZeroMorphisms PUnit
#synth CategoryTheory.Limits.HasZeroObject PUnit
#synth CategoryTheory.Simple (0 : PUnit)
example : False := by
  exact CategoryTheory.zero_not_simple PUnit
