import Mathlib

def isPrimeComp (n : ℕ) : Bool :=
  if n < 2 then false else
  Id.run do
    for i in [2:n] do
      if i * i > n then break
      if n % i == 0 then return false
    return true

#eval isPrimeComp (103^2 - 2)
#eval isPrimeComp (47^2 - 2)
#eval isPrimeComp (43^2 - 2)
