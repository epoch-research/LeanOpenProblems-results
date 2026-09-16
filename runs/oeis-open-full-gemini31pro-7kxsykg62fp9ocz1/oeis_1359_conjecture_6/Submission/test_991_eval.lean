import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec check (d : ℕ) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else check (d + 1)
    check 2

def nextPrime (n : ℕ) : ℕ :=
  if isPrime (n + 1) then n + 1
  else nextPrime (n + 1)

def nthPrime (n : ℕ) : ℕ :=
  if n == 0 then 2
  else nextPrime (nthPrime (n - 1))

#eval nthPrime 990
