import Mathlib

def checkPrimeLoop (n : ℕ) (d : ℕ) : Bool :=
  if d * d > n then true
  else if n % d == 0 then false
  else checkPrimeLoop n (d + 1)
termination_by n - d
decreasing_by sorry

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else checkPrimeLoop n 2

def countPrimesLoop (n : ℕ) (c : ℕ) (k : ℕ) : ℕ :=
  if k >= n then c
  else countPrimesLoop n (if isPrimeFast k then c + 1 else c) (k + 1)
termination_by n - k
decreasing_by sorry

def countPrimes (n : ℕ) : ℕ := countPrimesLoop n 0 0

lemma cp_7841 : countPrimes 7842 = 991 := by decide
