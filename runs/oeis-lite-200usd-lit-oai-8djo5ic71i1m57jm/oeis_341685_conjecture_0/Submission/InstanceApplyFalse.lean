import FormalConjectures.Util.ProblemImports

-- Test some seemingly dangerous false-conclusion theorems with concrete harmless choices.
example : False := by
  -- Category zero object simple contradiction? Try Type with PUnit? no expected to fail.
  apply?

-- More targeted: can category instances synthesize contradictions anywhere?
#synth CategoryTheory.Category Empty
#synth CategoryTheory.Limits.HasZeroObject Empty
#synth CategoryTheory.Limits.HasZeroMorphisms Empty
#synth CategoryTheory.Simple (0 : Empty)

#synth CategoryTheory.Category (Discrete Empty)
#synth CategoryTheory.Limits.HasZeroObject (Discrete Empty)
#synth CategoryTheory.Limits.HasZeroMorphisms (Discrete Empty)
