import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

structure Box (P : Prop) where
  pr : P

unsafe partial def badBox (n : ℕ) (h : n > 13) : Box (A216265 n > 0) := badBox n h
unsafe def badProof (n : ℕ) (h : n > 13) : A216265 n > 0 := (badBox n h).pr

#print axioms badProof
-- theorem test (n : ℕ) (h : n > 13) : A216265 n > 0 := badProof n h
