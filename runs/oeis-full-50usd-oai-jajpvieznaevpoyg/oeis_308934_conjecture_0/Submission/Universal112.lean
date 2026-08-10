import FormalConjectures.Util.ProblemImports
open Nat
-- Can four squares imply x^2+y^2+z^2+2w^2? Test with exact? no.
example (n : ℕ) : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + 2*d^2 = n := by
  -- try to use four squares? exact? maybe theorem exists
  exact?
