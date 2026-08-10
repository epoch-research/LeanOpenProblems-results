import FormalConjectures.Util.ProblemImports
open Finset Nat
open scoped BigOperators

def bmodStep (m : Nat) (state : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  let (k, bprev, bcur, c, invden) := state
  let term := (bcur * ((c * c % m) * c % m) % m) * invden % m
  let invNeg : Nat := 0 -- placeholder
  (k+1, bcur, (m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m - 47*bcur % m + m - 4096*bprev % m)%m, c, invden)

#eval (130579^3)
#eval (2225898497228688 < 130579^3)
