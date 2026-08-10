import FormalConjectures.Util.ProblemImports

open CategoryTheory

#check CategoryTheory.zero_not_simple
#check ModuleCat.of
#check (0 : ModuleCat ℚ)
#check (ModuleCat.of ℚ (PUnit))
#check ModuleCat.simple_of_isSimpleModule
#check ModuleCat.isSimpleModule_of_simple
#check IsSimpleModule

#synth CategoryTheory.Limits.HasZeroMorphisms (ModuleCat ℚ)
#synth CategoryTheory.Limits.HasZeroObject (ModuleCat ℚ)
#synth Simple (0 : ModuleCat ℚ)
#synth IsSimpleModule ℚ (0 : ModuleCat ℚ)

example : False := by
  exact CategoryTheory.zero_not_simple (ModuleCat ℚ)
