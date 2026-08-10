import FormalConjectures.Util.ProblemImports
open CategoryTheory
open CategoryTheory.Limits
#synth Simple (0 : ModuleCat ℤ)
#synth Simple (0 : ModuleCat ℚ)
#synth Simple (0 : AddCommGrp)
#synth Simple (0 : SemiNormedGrp)
#synth Simple (0 : Condensed.{0} Ab.{0})
example : False := by
  exact CategoryTheory.zero_not_simple (ModuleCat ℤ)
