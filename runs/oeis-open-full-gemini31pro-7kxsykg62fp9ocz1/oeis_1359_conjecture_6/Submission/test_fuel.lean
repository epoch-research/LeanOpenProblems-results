import Mathlib

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

def checkPrimeLoop (n : ℕ) (d : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if d * d > n then true
    else if n % d == 0 then false
    else checkPrimeLoop n (d + 1) f

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else checkPrimeLoop n 2 n

def countPrimesLoop (n : ℕ) (c : ℕ) (k : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => c
  | f + 1 =>
    if k >= n then c
    else countPrimesLoop n (if isPrimeFast k then c + 1 else c) (k + 1) f

def countPrimes (n : ℕ) : ℕ := countPrimesLoop n 0 0 n

lemma cp_7842 : countPrimes 7842 = 991 := by decide
