import Mathlib

open Nat Finset
open scoped Nat.Prime

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

def check_all : IO Unit := do
  for n in [32:101] do
    if A236097_comp n == 0 then
      IO.println s!"Counterexample: {n}"

#eval check_all
