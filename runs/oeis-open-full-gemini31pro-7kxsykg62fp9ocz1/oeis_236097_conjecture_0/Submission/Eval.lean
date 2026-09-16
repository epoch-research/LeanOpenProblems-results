import Mathlib

open Nat Finset
open scoped Nat.Prime

-- Computable nth prime
partial def nth_prime_comp (n : ℕ) : ℕ :=
  let rec aux (count p : ℕ) : ℕ :=
    if count = n + 1 then p - 1
    else if (p).Prime then aux (count + 1) (p + 1)
    else aux count (p + 1)
  aux 0 2

def A236097_comp (n : ℕ) : ℕ := Id.run do
  let mut sum := 0
  for k in [1:n-2] do
    let p_val := k.totient + (n - k).totient / 2 + 1
    let p_prime := nth_prime_comp (p_val - 1)
    if p_val.Prime && (p_prime - p_val - 1).Prime && (p_prime - p_val + 1).Prime then
      sum := sum + 1
  return sum

#eval! A236097_comp 32
#eval! A236097_comp 33
#eval! A236097_comp 34
#eval! A236097_comp 35
#eval! A236097_comp 36
#eval! A236097_comp 37
#eval! A236097_comp 38
