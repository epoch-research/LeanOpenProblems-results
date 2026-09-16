import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem foo : ∃ k, (Nat.digits 10 (Nat.factorial k)).count 6 = 24 := answer(sorry)
