import FormalConjectures.Util.ProblemImports

theorem omega_neg_div_bug (x : ℤ) (y : ℤ) (h : y = x / -2) : False := by
  omega
