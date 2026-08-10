import FormalConjectures.Util.ProblemImports
open CategoryTheory

#synth CategoryTheory.Limits.HasZeroObject (Discrete PUnit)
#synth CategoryTheory.Limits.HasZeroMorphisms (Discrete PUnit)
#synth CategoryTheory.Simple (0 : Discrete PUnit)
#synth CategoryTheory.Limits.HasZeroObject (Type)
#synth CategoryTheory.Limits.HasZeroMorphisms (Type)
#synth CategoryTheory.Simple (0 : Type)
#synth PreirreducibleSpace PUnit
#synth T2Space PUnit
#synth Nontrivial PUnit
#synth PreirreducibleSpace (ULift Bool)
#synth T2Space (ULift Bool)
#synth Nontrivial (ULift Bool)

example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)

example : False := by
  exact not_preirreducible_nontrivial_t2 (ULift Bool)
