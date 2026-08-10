import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

instance (priority := high) (n : ℕ) : Nonempty (0 < A271510 n) :=
  inferInstance
