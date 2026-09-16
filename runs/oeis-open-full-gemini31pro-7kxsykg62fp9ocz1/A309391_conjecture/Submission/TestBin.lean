import Submission.Spec

def binary_split_H (a b : ℕ) : ℕ × ℕ :=
  if b - a == 1 then
    (1, a)
  else
    let m := (a + b) / 2
    let (n1, d1) := binary_split_H a m
    let (n2, d2) := binary_split_H m b
    -- we should reduce fractions?
    -- for exact H, we must. But reducing fractions with gcd takes time.
    (n1 * d2 + n2 * d1, d1 * d2)

#eval 1
