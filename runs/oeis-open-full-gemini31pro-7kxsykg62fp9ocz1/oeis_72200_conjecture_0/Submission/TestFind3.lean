import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem test : ∃ k, (Nat.digits 10 (Nat.factorial k)).count 6 = 1 := by
  use 3
  decide
