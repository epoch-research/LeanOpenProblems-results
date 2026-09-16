import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

#eval a 38
