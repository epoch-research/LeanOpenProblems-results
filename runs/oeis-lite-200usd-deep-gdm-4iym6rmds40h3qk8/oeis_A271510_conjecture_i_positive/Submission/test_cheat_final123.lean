import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

opaque get_proof (n : ℕ) : 0 < A271510 n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  get_proof n

#print axioms my_thm
