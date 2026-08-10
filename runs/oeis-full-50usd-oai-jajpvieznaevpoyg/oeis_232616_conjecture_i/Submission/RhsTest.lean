import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

example (n : ℕ) (hn : 0 < n) : 0 < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  have hprime : Nat.Prime (Nat.nth Nat.Prime (n - 1)) := Nat.prime_nth_prime (n - 1)
  have hgt1 : 1 < Nat.nth Nat.Prime (n - 1) := hprime.one_lt
  omega
