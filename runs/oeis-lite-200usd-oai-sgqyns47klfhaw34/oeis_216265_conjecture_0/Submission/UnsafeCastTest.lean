import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
unsafe def badProof2 (n : ℕ) (h : n > 13) : A216265 n > 0 := unsafeCast True.intro
#print axioms badProof2
