import FormalConjectures.Util.ProblemImports
#check Erased.out_proof
#check Erased.mk
#synth Inhabited (Erased False)
#synth Nonempty (Erased False)
example : False := by
  fail_if_success exact Erased.out_proof (a := (default : Erased False))
  sorry
