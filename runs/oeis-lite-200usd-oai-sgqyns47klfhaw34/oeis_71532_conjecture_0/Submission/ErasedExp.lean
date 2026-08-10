import FormalConjectures.Util.ProblemImports
#print Erased
#check Erased.mk
#check Erased.out
#check Erased.out_proof
#synth Inhabited (Erased False)
#synth Nonempty (Erased False)
example : False := Erased.out_proof (default : Erased False)
#print axioms ErasedExp._example_1
