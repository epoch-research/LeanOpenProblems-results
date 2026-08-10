import FormalConjectures.Util.ProblemImports
#synth Infinite (Fin 0)
#synth Infinite (Fin 1)
#synth Infinite (ZMod 1)
#synth Fintype (ZMod 0)
#synth CharP (ZMod 2) 1
#synth PreirreducibleSpace Bool
#synth T2Space Bool
#synth Nontrivial Bool
#synth PreirreducibleSpace Prop
#synth T2Space Prop
#synth Nontrivial Prop
example : False := not_preirreducible_nontrivial_t2 Bool
example : False := not_preirreducible_nontrivial_t2 Prop
