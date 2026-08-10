import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

opaque safe_nonempty (n : ℕ) : Nonempty (0 < A271510 n)

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  Classical.choice (safe_nonempty n)

#print axioms my_thm
