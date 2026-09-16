import Mathlib
open Nat Finset

def myTotient (n : ℕ) : ℕ :=
  (Finset.Ico 1 (n + 1)).filter (fun x => x.gcd n == 1) |>.card

def isPrime (n : ℕ) : Bool :=
  n.Prime

-- This will be very slow in #eval because of Nat.Prime being Prop, so we use a computable one
def compPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    Id.run <| do
      for i in [2:n] do
        if n % i == 0 then return false
      return true

def nthPrime (n : ℕ) : ℕ :=
  Id.run <| do
    let mut p := 2
    let mut count := 0
    while count < n do
      p := p + 1
      if compPrime p then count := count + 1
    return p

def A236097 (n : ℕ) : ℕ :=
  Id.run <| do
    let mut sum := 0
    for k in [1:n-2] do
      let p_val := myTotient k + myTotient (n - k) / 2 + 1
      if compPrime p_val then
        let p_prime := nthPrime (p_val - 1)
        if compPrime (p_prime - p_val - 1) && compPrime (p_prime - p_val + 1) then
          sum := sum + 1
    return sum

#eval A236097 32
#eval A236097 33
#eval A236097 34
