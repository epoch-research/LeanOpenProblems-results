import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

theorem test_prime_large : (1999993 : Nat).Prime := by decide
