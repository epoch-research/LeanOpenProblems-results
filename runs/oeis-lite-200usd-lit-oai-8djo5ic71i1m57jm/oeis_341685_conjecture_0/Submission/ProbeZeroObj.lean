import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits

#check (0 : TypeCat)
#check (0 : ModuleCat ℚ)
#check (0 : FintypeCat)
#check (0 : SemiNormedGrp)
#check (0 : AddCommGrpCat)
#check (0 : CommRingCat)
#check (0 : RingCat)
#check (0 : GrpCat)
#check zero_not_simple

example : False := by
  exact CategoryTheory.zero_not_simple (ModuleCat ℚ)
