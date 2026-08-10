import FormalConjectures.Util.ProblemImports
#print Erased
#check Erased.out
#check Erased.out_proof
#check Erased.mk
#check (inferInstance? : Option (Inhabited (Erased False)))
#check (inferInstance? : Option (Nonempty (Erased False)))
#synth Inhabited (Erased True)
#synth Inhabited (Erased False)
#synth Nonempty (Erased False)
#print axioms Erased.out_proof
