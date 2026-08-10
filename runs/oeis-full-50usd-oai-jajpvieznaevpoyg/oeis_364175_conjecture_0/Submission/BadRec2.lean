import FormalConjectures.Util.ProblemImports

theorem bad : ∀ r : ℕ, False
  | 0 => bad 0
  | r+1 => bad r
