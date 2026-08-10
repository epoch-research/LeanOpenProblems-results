import FormalConjectures.Util.ProblemImports
open Nat Finset
example (n : ℕ) (hn : n > 1) : ∃ a b c d x y : ℕ,
    (2^a * 3^b)^2 + (2^c * 3^d)^2 + x^2 + 2*y^2 = n := by
  exact?
