import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

theorem next_prime_gt (r : ℕ) : r < next_prime r := by
  sorry
