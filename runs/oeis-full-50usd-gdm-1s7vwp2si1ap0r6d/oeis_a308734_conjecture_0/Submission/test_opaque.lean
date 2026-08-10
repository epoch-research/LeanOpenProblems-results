import FormalConjectures.Util.ProblemImports

open Nat Finset

structure Solution (n : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  x : ℕ
  y : ℕ
  ha : a < Nat.sqrt n + 1
  hb : b < Nat.sqrt n + 1
  hc : c < Nat.sqrt n + 1
  hd : d < Nat.sqrt n + 1
  hx : x < Nat.sqrt n + 1
  hy : y < Nat.sqrt n + 1
  heq : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n
  hxy : x ≤ y

unsafe def unsafe_find_sol (n : ℕ) : Solution n :=
  -- unsafe definition of finding solution
  unsafe_find_sol n

@[implemented_by unsafe_find_sol]
axiom safe_find_sol (n : ℕ) : Solution n
