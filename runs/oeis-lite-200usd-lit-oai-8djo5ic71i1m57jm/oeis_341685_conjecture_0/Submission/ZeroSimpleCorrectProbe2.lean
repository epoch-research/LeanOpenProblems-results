import FormalConjectures.Util.ProblemImports

open CategoryTheory
open CategoryTheory.Limits

#check (0 : ModuleCat ℚ)
#check (0 : ModuleCat.{0} ℚ)
#check (0 : ModuleCat.{1} ℚ)
#check (Limits.HasZeroObject.zero : ModuleCat ℚ)
#check (ModuleCat.of ℚ PUnit)
#check simple_of_isSimpleModule
#check isSimpleModule_of_simple
#check simple_iff_isSimpleModule'

#synth Simple (ModuleCat.of ℚ PUnit)
#synth IsSimpleModule ℚ PUnit

example : False := by
  haveI : Simple (ModuleCat.of ℚ PUnit) := inferInstance
  -- is this the zero object?
  have hz : (ModuleCat.of ℚ PUnit) = (0 : ModuleCat ℚ) := by
    ext x
    exact PUnit.ext _ _
  rw [← hz] at (CategoryTheory.zero_not_simple (ModuleCat ℚ))
  exact CategoryTheory.zero_not_simple (ModuleCat ℚ)
