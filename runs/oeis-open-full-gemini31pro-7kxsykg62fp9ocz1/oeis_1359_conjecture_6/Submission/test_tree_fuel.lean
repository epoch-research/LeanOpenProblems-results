import Mathlib

set_option maxHeartbeats 20000000

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

def countPrimesTree (low high fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if high <= low then 0
    else if high == low + 1 then
      if isPrimeFast low then 1 else 0
    else
      let mid := (low + high) / 2
      countPrimesTree low mid f + countPrimesTree mid high f

def countPrimes (n : ℕ) : ℕ := countPrimesTree 0 n 30

lemma cp_7842 : countPrimes 7842 = 991 := by decide
