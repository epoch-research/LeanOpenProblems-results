import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

example (z : ℕ) : (3 * z + 1) * (3 * z + 1) = 3 * (z * (3 * z + 2)) + 1 := by
  ring

