import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

def check1 (n : ℕ) : Bool := if 2 < n then a n > 0 else true
def check2 (n : ℕ) : Bool := (a n == 1) == (n == 5 || n == 8 || n == 13)

#eval (List.range 40).all fun n => check1 n && check2 n
