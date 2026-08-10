import FormalConjectures.Util.ProblemImports
open Finset Nat Int
example (n : ℕ) : n = n := by decide
example (n : ℕ) : (n : ℤ) ≡ (n : ℤ) [ZMOD n] := by decide
