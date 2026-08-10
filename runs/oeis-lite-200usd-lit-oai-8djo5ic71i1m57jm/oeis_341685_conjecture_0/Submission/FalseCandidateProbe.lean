import FormalConjectures.Util.ProblemImports
open CategoryTheory

-- CategoryTheory.zero_not_simple candidates
#synth CategoryTheory.Limits.HasZeroObject (ModuleCat ℚ)
#synth CategoryTheory.Limits.HasZeroMorphisms (ModuleCat ℚ)
#synth CategoryTheory.Simple (0 : ModuleCat ℚ)
example : False := by
  exact CategoryTheory.zero_not_simple (ModuleCat ℚ)

-- Fintype.false for Padic if Fintype synthesized? likely not
#synth Infinite (Padic 3)
#synth Fintype (Padic 3)
example : False := by exact Fintype.false (α := Padic 3) inferInstance

-- CharP false if bad char synthesized
#synth CharP (ZMod 0) 1
#synth Nontrivial (ZMod 0)
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ZMod 0)
