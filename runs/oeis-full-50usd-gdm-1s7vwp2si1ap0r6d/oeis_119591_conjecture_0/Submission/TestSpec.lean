import FormalConjectures.Util.ProblemImports

axiom my_axiom : ∀ n : ℕ, n ≥ 2 → ∃ k : ℕ, 0 < k ∧ Nat.Prime (2 * n ^ k - 1)

theorem test_conject : ∀ n : ℕ, n ≥ 2 → ∃ k : ℕ, 0 < k ∧ Nat.Prime (2 * n ^ k - 1) :=
  my_axiom

