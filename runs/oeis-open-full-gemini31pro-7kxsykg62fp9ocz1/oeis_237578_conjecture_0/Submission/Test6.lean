import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

#eval a 15
#eval a 16
#eval a 17
#eval a 18
#eval a 19
#eval a 20
#eval a 21
