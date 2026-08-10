import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits

#check CategoryTheory.Simple
#check CategoryTheory.simple_def
#check CategoryTheory.zero_not_simple
#check (⟨PUnit.unit⟩ : Discrete PUnit)
#check (⊥_ (⟨PUnit.unit⟩ : Discrete PUnit))

noncomputable instance : CategoryTheory.Simple (⟨PUnit.unit⟩ : Discrete PUnit) := by
  rw [CategoryTheory.simple_def]
  constructor
  · intro Y f hf
    infer_instance
  · intro Y f hf
    infer_instance

example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)
