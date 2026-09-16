import FormalConjectures.Util.ProblemImports

open Nat
set_option maxRecDepth 20000000
set_option maxHeartbeats 20000000
lemma count_primes : (Finset.filter Nat.Prime (Finset.Icc 2 7841)).card = 991 := by decide
