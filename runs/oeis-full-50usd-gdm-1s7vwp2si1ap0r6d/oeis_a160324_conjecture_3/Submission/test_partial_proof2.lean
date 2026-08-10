import FormalConjectures.Util.ProblemImports

open Nat

partial def prove_exists (k : ℕ) : ∃ n : ℕ, n = k :=
  prove_exists k
