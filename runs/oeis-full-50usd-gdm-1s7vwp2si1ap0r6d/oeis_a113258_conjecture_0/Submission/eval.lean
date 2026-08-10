import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

#eval a 10 % 11069
