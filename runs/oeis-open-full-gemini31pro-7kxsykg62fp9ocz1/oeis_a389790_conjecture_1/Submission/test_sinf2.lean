import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

theorem next_prime_eq (r : ℕ) : next_prime r = sInf {k : ℕ | Nat.Prime k ∧ r < k} := rfl
