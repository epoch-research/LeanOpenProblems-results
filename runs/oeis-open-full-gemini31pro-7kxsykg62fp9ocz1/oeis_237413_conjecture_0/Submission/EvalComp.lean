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
    for i in [2:500] do
      if isPrimeComp i then res := res ++ [i]
    return res

def p_j_comp (j : ℕ) : ℕ :=
  primes.getD (j - 1) 0

def A237413_comp (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun k ↦
    let m := n - k
    let pk := p_j_comp k
    let pm := p_j_comp m
    let ppm := p_j_comp pm
    let p1 := pk ^ 2 - 2
    let p2 := pm ^ 2 - 2
    let p3 := ppm ^ 2 - 2
    if isPrimeComp p1 ∧ isPrimeComp p2 ∧ isPrimeComp p3 then 1 else 0

#eval (List.range 30).map A237413_comp
