import FormalConjectures.Util.ProblemImports

open Nat

theorem test : sqrt (totient 1 * totient 8) ^ 2 = totient 1 * totient 8 := by
  decide
