import Mathlib

open Nat Int Finset

def a_eval (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun k : ℕ =>
    (
      (-1 : ℤ) ^ (n + k + 1) *
      (n.choose k : ℤ) *
      ((Nat.choose (n + k - 1) k : ℤ) ^ 2)
    )
  ).natAbs

#eval a_eval 1
#eval a_eval 2
#eval a_eval 3
#eval a_eval 4
#eval a_eval 5
#eval a_eval 7
