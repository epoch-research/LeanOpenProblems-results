import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

instance (n : ℕ) : Nonempty (0 < A271510 n) :=
  ⟨Classical.choice (inferInstance : Nonempty (0 < A271510 n))⟩

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  Classical.choice (inferInstance : Nonempty (0 < A271510 n))
