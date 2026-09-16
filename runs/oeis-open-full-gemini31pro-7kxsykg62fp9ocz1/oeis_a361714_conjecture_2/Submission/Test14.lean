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

#eval decide ((a_eval (7 ^ 2) : ℤ) ≡ (a_eval (7 ^ 1) : ℤ) [ZMOD (7 ^ (3 * 2 + 3) : ℤ)])
