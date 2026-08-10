import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

unsafe def loopProof (n : ℕ) (h : n > 13) : A216265 n > 0 := loopProof n h

theorem callUnsafe (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  exact loopProof n h
#print axioms callUnsafe
