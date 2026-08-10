import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits
#print CategoryTheory.Simple
#print CategoryTheory.Limits.HasZeroObject
#check (0 : ModuleCat ℚ)
#check (0 : Type*)
#check (⊥ : Discrete PUnit)
#check (Limits.HasZeroObject.zero (Discrete PUnit))
#check (CategoryTheory.Limits.HasZeroObject.zero (Discrete PUnit))
#check (CategoryTheory.Limits.zero (Discrete PUnit))
#check (CategoryTheory.Limits.hasZeroObject_pUnit)
example : False := by
  haveI := (inferInstance : HasZeroObject (Discrete PUnit))
  let Z := CategoryTheory.Limits.HasZeroObject.zero (Discrete PUnit)
  have hS : Simple Z := by
    infer_instance
  exact CategoryTheory.zero_not_simple (Discrete PUnit)
