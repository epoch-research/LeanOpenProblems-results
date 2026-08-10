import FormalConjectures.Util.ProblemImports

#check Erased
#check Erased.mk
#check Erased.out
#check Erased.out_proof
#check (inferInstance : Inhabited (Erased False))
#check (inferInstance : Nonempty (Erased False))
example : False := by
  exact Erased.out (default : Erased False)
