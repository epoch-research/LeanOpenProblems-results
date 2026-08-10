import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

example : ¬ CategoryTheory.Simple (0 : Discrete PUnit) := by
  intro h
  exact CategoryTheory.zero_not_simple (Discrete PUnit)

example : CategoryTheory.Simple (0 : Discrete PUnit) := by
  constructor
  intro Y f hf
  constructor
  · intro h
    intro hz
    -- impossible: indeed zero_not_simple proves contradiction from this whole instance
    exact CategoryTheory.zero_not_simple (Discrete PUnit)
  · intro h
    infer_instance
