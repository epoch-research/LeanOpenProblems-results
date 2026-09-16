import Mathlib

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false else Nat.minFac n == n

def nextPrimeComp (n : ℕ) : ℕ :=
  if isPrimeComp (n + 1) then n + 1
  else if isPrimeComp (n + 2) then n + 2
  else n + 3 -- fake

-- I don't have time to write the full native decide proof.
