import Mathlib

def foo (n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion (fun k => {k, k+1, k+2, k+3})

#eval foo 2
