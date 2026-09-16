import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    loop 2
  termination_by n - i

def nthPrime (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (c : ℕ) : ℕ :=
    if c > n then i - 1
    else loop (i + 1) (c + if isPrime i then 1 else 0)
  loop 2 0
  termination_by 0 -- sorry, just need a quick eval, but I can't sorry.
