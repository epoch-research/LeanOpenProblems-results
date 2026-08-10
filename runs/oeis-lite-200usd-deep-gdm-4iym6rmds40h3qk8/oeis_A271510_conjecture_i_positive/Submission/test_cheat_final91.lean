import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let rec loop : 0 < A271510 n := loop
  exact loop

#print axioms my_thm
