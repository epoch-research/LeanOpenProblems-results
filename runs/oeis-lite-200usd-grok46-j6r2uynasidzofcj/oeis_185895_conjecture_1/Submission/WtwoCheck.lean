import FormalConjectures.Util.ProblemImports

open Nat

def W : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 =>
    if n < k + 1 then W n k
    else W n k + (k + 1).factorial * W (n - (k + 1)) k

def checkWtwo (M : ℕ) : Bool :=
  (List.range (M + 1)).all fun k =>
    decide (k < 81 || W (2 * k) k ≤ 4 * k.factorial * (k - 1).factorial)

example : checkWtwo 90 = true := by native_decide
