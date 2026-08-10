import FormalConjectures.Util.ProblemImports
open Finset Nat

example (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    0 ≤ ∑ a ∈ Finset.Icc 1 (p / 2), legendreSym p (a : ℤ) := by
  apply?
