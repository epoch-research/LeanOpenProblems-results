import Mathlib

def is_prime (n : ℕ) : Bool :=
  if n < 2 then false
  else List.all (List.range n) (fun d => if d < 2 then true else n % d != 0)

def check_goldbach (n : ℕ) : Bool :=
  if n % 2 != 0 || n <= 2 then true
  else List.any (List.range n) (fun p => is_prime p && is_prime (n - p))

#eval List.all (List.range 1000) check_goldbach
