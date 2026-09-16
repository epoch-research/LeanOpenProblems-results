import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun s => if Nat.Prime (n^2 + s^2) then 1 else 0

#eval Nat.primeCounting 46341
#eval a 46341
