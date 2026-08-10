import FormalConjectures.Util.ProblemImports

example : ¬ Nat.Prime 42841680111100223 :=
  Nat.not_prime_of_dvd_of_lt (m := 17) (by decide) (by decide) (by decide)
