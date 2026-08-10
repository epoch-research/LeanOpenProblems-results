import FormalConjectures.Util.ProblemImports
#check Squarefree
#print Squarefree
example : ¬ Squarefree (0:ℤ) := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible]
  · push_neg
    use (2:ℤ)
    constructor
    · exact (Int.prime_two).irreducible
    · simp
  · use (2:ℤ)
    exact (Int.prime_two).irreducible
