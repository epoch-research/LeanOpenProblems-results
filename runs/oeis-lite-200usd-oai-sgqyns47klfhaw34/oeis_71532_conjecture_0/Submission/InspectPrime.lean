import FormalConjectures.Util.ProblemImports
#print Prime
#check prime_def_lt
#check prime_def
example : ¬ Prime (0 : PUnit) := by infer_instance <;> exact not_prime_zero
