import FormalConjectures.Util.ProblemImports

theorem loop (n : ℕ) : n = n := by
  exact loop n
termination_by 0

theorem loop2 (n : ℕ) : n = n := by
  exact loop2 (n+1)
termination_by n
