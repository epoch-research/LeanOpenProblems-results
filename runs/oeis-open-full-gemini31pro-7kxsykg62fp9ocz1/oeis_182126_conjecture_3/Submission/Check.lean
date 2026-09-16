import Mathlib

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0
  else (p_n n * p_n (n + 1)) % p_n (n + 2)
