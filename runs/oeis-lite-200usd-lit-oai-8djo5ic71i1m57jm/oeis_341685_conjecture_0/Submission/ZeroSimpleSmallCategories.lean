import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits
#synth Category PUnit
#synth HasZeroMorphisms PUnit
#synth HasZeroObject PUnit
#synth Simple (0 : PUnit)
example : False := CategoryTheory.zero_not_simple PUnit
#synth Category (Discrete PUnit)
#synth HasZeroMorphisms (Discrete PUnit)
#synth HasZeroObject (Discrete PUnit)
#synth Simple (0 : Discrete PUnit)
example : False := CategoryTheory.zero_not_simple (Discrete PUnit)
#synth Category (SingleObj PUnit)
#synth HasZeroMorphisms (SingleObj PUnit)
#synth HasZeroObject (SingleObj PUnit)
#synth Simple (0 : SingleObj PUnit)
example : False := CategoryTheory.zero_not_simple (SingleObj PUnit)
