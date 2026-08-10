import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
#synth Category (Discrete PUnit)
#synth HasZeroMorphisms (Discrete PUnit)
#synth HasZeroObject (Discrete PUnit)
#check (0 : Discrete PUnit)
#synth Simple (0 : Discrete PUnit)
example : False := CategoryTheory.zero_not_simple (Discrete PUnit)
