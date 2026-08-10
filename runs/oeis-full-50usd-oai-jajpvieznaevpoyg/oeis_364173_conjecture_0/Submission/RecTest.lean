import FormalConjectures.Util.ProblemImports
-- legitimate recursion on n proving True
theorem recTrue : ∀ n : ℕ, True
  | 0 => trivial
  | n+1 => recTrue n
#print axioms recTrue
-- impossible recursion attempting False
theorem recFalse : ∀ n : ℕ, False
  | 0 => by exact recFalse 0
  | n+1 => recFalse n
#print axioms recFalse
