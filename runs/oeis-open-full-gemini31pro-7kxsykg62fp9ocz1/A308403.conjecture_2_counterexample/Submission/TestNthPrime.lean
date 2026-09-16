import Mathlib

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false else Nat.minFac n == n

def nextPrimeComp (n : ℕ) : ℕ :=
  if isPrimeComp (n + 1) then n + 1
  else if isPrimeComp (n + 2) then n + 2
  else if isPrimeComp (n + 3) then n + 3
  else n + 4 -- just a mock

