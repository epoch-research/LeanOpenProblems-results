import Submission.Spec
open Nat Int Finset

def a_eval (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun k : ℕ =>
    (
      (-1 : ℤ) ^ (n + k + 1) *
      (n.choose k : ℤ) *
      ((Nat.choose (n + k - 1) k : ℤ) ^ 2)
    )
  ).natAbs

#eval ((a_eval (7^2) : ℤ) - (a_eval (7^1) : ℤ)) % (7^9 : ℤ)
#eval ((a_eval (11^2) : ℤ) - (a_eval (11^1) : ℤ)) % (11^9 : ℤ)

