import FormalConjectures.Util.ProblemImports
open CategoryTheory
open CategoryTheory.Limits

-- Try concrete category PUnit with discrete/trivial category instances.
#synth Category PUnit
#synth HasZeroMorphisms PUnit
#synth HasZeroObject PUnit
#check CategoryTheory.zero_not_simple

example : False := by
  haveI : Simple (0 : PUnit) := by
    constructor
    intro Y f hf
    constructor
    · intro _ hzero
      -- impossible branch? try simp
      simp at hzero
    · intro h
      infer_instance
  exact CategoryTheory.zero_not_simple PUnit
