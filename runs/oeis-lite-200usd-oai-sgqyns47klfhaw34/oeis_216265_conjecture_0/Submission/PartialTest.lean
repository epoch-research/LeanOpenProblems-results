import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

partial def badProof (n : ℕ) (h : n > 13) : A216265 n > 0 := badProof n h

#print axioms badProof
example (n : ℕ) (h : n > 13) : A216265 n > 0 := badProof n h
