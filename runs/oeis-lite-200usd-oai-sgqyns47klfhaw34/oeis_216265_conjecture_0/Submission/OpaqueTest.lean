import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

opaque badOpaque (n : ℕ) (h : n > 13) : A216265 n > 0
#print axioms badOpaque
example (n : ℕ) (h : n > 13) : A216265 n > 0 := badOpaque n h
