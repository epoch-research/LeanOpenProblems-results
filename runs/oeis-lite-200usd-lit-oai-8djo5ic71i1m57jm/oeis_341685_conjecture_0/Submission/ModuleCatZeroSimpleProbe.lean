import FormalConjectures.Util.ProblemImports

open CategoryTheory
open ModuleCat

#check ModuleCat.simple_of_isSimpleModule
#synth Category (ModuleCat ℚ)
#synth CategoryTheory.Limits.HasZeroMorphisms (ModuleCat ℚ)
#synth CategoryTheory.Limits.HasZeroObject (ModuleCat ℚ)
#synth Simple (0 : ModuleCat ℚ)
#synth IsSimpleModule ℚ (0 : ModuleCat ℚ)

example : False := by
  exact CategoryTheory.zero_not_simple (ModuleCat ℚ)
