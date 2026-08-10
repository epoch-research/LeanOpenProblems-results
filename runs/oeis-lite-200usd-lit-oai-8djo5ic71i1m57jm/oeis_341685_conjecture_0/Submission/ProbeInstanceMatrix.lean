import FormalConjectures.Util.ProblemImports

-- Common suspicious types
#synth Infinite Empty
#synth Infinite PEmpty
#synth Infinite PUnit
#synth Infinite Unit
#synth Infinite (Fin 0)
#synth Infinite (Fin 1)
#synth Infinite (ULift Empty)
#synth Infinite (PLift False)
#synth Infinite (Subtype (fun n : ℕ => False))
#synth Subsingleton ℕ
#synth Finite ℕ
#synth Fintype ℕ
#synth Finite ℚ
#synth Fintype ℚ
#synth Subsingleton ℚ
#synth Nontrivial Empty
#synth Nontrivial PUnit
#synth Field Empty
#synth Field PEmpty
#synth Field (Fin 0)
#synth Field (Fin 1)
#synth Field (ULift Empty)
#synth Field (PLift False)
