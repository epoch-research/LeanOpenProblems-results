import FormalConjectures.Util.ProblemImports

open Nat

example : ¬ Nat.Prime 42841680111100223 := by
  apply Nat.not_prime_of_dvd_of_lt (m := 17)
  · decide
  · decide
  · decide
