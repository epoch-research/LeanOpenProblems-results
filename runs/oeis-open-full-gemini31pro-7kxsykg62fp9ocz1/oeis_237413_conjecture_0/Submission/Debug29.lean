import Mathlib

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false else
  Id.run do
    for i in [2:n] do
      if i * i > n then break
      if n % i == 0 then return false
    return true

def primes : List ℕ :=
  Id.run do
    let mut res := []
    for i in [2:1000] do
      if isPrimeComp i then res := res ++ [i]
    return res

def p_j_comp (j : ℕ) : ℕ :=
  primes.getD (j - 1) 0

#eval isPrimeComp (107^2 - 2)
#eval isPrimeComp (587^2 - 2)
