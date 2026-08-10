import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

noncomputable instance simpleZeroDiscrete : CategoryTheory.Simple (0 : Discrete PUnit) where
  mono_isIso_iff_nonzero := by
    intro Y f hf
    constructor
    · intro _ hz
      exact CategoryTheory.zero_not_simple (Discrete PUnit)
    · intro _
      infer_instance

example : False := CategoryTheory.zero_not_simple (Discrete PUnit)
#print axioms simpleZeroDiscrete
#print axioms _example
