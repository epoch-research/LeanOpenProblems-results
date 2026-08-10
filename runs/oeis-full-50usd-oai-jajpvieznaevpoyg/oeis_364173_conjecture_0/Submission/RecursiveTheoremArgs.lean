import FormalConjectures.Util.ProblemImports

theorem rec_bad (n : ℕ) : False := by
  exact rec_bad n
#print axioms rec_bad

theorem rec_bad2 : ∀ n : ℕ, False
| 0 => rec_bad2 0
| n+1 => rec_bad2 n
#print axioms rec_bad2
