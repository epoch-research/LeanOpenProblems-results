import FormalConjectures.Util.ProblemImports
open Nat Finset

theorem check_352259 : ∃ w x y z : ℕ, 352259 = 2 * w^4 + 3 * x^2 + y^2 + z^2 + x * y * z := by
  decide
