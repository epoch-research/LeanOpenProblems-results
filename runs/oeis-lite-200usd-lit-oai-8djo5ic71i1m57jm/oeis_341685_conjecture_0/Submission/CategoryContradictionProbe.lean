import FormalConjectures.Util.ProblemImports

open CategoryTheory

-- Inspect the suspicious theorem
#check CategoryTheory.zero_not_simple
#print axioms CategoryTheory.zero_not_simple

-- Try common categories
#synth Category (Type)
#synth Limits.HasZeroMorphisms (Type)
#synth Limits.HasZeroObject (Type)
#synth Simple (0 : Type)

example : False := by
  exact CategoryTheory.zero_not_simple (Type)
