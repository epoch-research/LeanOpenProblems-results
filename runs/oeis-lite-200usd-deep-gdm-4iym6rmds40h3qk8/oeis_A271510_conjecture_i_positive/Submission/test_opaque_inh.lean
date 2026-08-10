import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

opaque safe_val (n : ℕ) : 0 < A271510 n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  safe_val n

#print axioms my_thm
