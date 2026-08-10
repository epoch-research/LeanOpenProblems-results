import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits

example : ¬ CategoryTheory.Simple (0 : Discrete PUnit) := by
  intro h
  exact CategoryTheory.zero_not_simple (Discrete PUnit)

-- If the following could be filled, we'd get False; it should expose impossible obligation.
example : CategoryTheory.Simple (0 : Discrete PUnit) := by
  constructor
  intro Y f hf
  constructor
  · intro h
    -- goal f ≠ 0; but in discrete punit all morphisms are equal
    intro hz
    exact False.elim ?_
  · intro h
    infer_instance
