import Mathlib
open Nat Finset

def A236097_val (n : ℕ) : ℕ := Id.run do
  let mut sum := 0
  for k in [1:n-2] do
    let p_val := k.totient + (n - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime && (p_prime - p_val - 1).Prime && (p_prime - p_val + 1).Prime then
      sum := sum + 1
  return sum

#eval A236097_val 32
