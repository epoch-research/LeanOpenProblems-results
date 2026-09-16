import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

#eval a 1
#eval a 2
#eval a 3
#eval a 4
#eval a 5
#eval a 6
#eval a 7
#eval a 8
#eval a 9
#eval a 10
#eval a 11
#eval a 12
#eval a 13
#eval a 14
#eval a 20
