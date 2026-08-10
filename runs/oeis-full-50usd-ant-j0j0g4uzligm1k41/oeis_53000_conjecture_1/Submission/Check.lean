import Mathlib

open Nat

-- computable smallest prime > m
def nextPrimeGt (m : ℕ) : ℕ :=
  let rec go (fuel : ℕ) (k : ℕ) : ℕ :=
    match fuel with
    | 0 => 0
    | fuel+1 => if Nat.Prime k then k else go fuel (k+1)
  go (m*m + m + 100) (m+1)

def a053 (n : ℕ) : ℕ := nextPrimeGt (n^2) - n^2

-- check a053 n ≤ 1 + totient n for n = 1..200
#eval (List.range 201).filter (fun n => n > 0 && !(a053 n ≤ 1 + Nat.totient n))
#eval (List.range 201).filter (fun n => n > 0 && (a053 n == 1 + Nat.totient n))
