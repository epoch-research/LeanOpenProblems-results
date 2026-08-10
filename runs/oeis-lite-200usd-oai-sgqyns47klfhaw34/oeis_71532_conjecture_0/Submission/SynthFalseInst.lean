import FormalConjectures.Util.ProblemImports
#synth NonAssocSemiring (ZMod 1)
#synth CharP (ZMod 1) 1
#synth Nontrivial (ZMod 1)
example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
