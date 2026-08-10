import FormalConjectures.Util.ProblemImports
example (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : False := by
  omega
