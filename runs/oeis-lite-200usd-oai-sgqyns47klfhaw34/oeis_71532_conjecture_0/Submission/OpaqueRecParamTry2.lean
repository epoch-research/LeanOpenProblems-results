import FormalConjectures.Util.ProblemImports
opaque oNat : Nat
opaque p2 : (n : Nat) → n < oNat → False
| 0, h => p2 1 (by omega)
| n+1, h => p2 n (by omega)
#print axioms p2
