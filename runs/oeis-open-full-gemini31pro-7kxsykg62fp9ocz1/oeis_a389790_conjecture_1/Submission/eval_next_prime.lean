import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

#eval next_prime 10
