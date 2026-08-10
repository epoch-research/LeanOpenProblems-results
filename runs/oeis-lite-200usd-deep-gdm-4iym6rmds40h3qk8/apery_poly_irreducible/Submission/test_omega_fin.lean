import FormalConjectures.Util.ProblemImports

theorem omega_fin (n : ℕ) (x : Fin n) (h : n = 0) : False := by
  omega
