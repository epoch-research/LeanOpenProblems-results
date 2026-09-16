import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem foo : (Nat.digits 10 (Nat.factorial 129)).count 6 = 23 := answer(by decide)
