import FormalConjectures.Util.ProblemImports
open Classical

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma next_prime_eq_zero (r : ℕ) : next_prime r = 0 := by
  sorry
