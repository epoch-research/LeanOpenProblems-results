import FormalConjectures.Util.ProblemImports
set_option synthInstance.maxHeartbeats 100000
#synth NonAssocSemiring (ZMod 1)
#synth CharP (ZMod 1) 1
#synth Nontrivial (ZMod 1)
#synth Subsingleton (ZMod 1)
#synth Finite (ZMod 1)
#synth Fintype (ZMod 1)

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)

#synth NonAssocSemiring (Fin 1)
#synth CharP (Fin 1) 1
#synth Nontrivial (Fin 1)
