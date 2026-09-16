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

def check_m (m : ℕ) : Bool :=
    let pm := p_j_comp m
    let ppm := p_j_comp pm
    let p2 := pm ^ 2 - 2
    let p3 := ppm ^ 2 - 2
    isPrimeComp p2 ∧ isPrimeComp p3

#eval (List.range 29).map check_m
