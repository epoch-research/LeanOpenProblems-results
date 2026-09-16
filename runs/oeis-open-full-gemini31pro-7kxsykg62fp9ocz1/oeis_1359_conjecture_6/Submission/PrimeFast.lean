import Mathlib

def minFacAux (n : ℕ) (k : ℕ) : ℕ :=
  if h : n < k * k then n
  else if n % k == 0 then k
  else minFacAux n (k + 2)
termination_by n - k * k
decreasing_by sorry

def minFacFast (n : ℕ) : ℕ :=
  if n % 2 == 0 then 2
  else minFacAux n 3

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else minFacFast n == n

