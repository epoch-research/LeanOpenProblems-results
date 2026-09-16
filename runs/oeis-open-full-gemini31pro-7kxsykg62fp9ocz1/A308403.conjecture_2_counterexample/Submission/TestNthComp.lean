import Mathlib

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false else Nat.minFac n == n

def nextPrimeComp (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) :=
    if isPrimeComp i then i else loop (i + 1)
  loop (n + 1)

def nthPrimeComp : ℕ → ℕ
  | 0 => 2
  | k + 1 => nextPrimeComp (nthPrimeComp k)

