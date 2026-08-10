import FormalConjectures.Util.ProblemImports
open Nat Finset

example (n : ℕ) : ∃ A B C D : ℕ, A^2 + 2*B^2 + C^4 + 4*D^4 + C^2*D^2 = n := by
  apply?
