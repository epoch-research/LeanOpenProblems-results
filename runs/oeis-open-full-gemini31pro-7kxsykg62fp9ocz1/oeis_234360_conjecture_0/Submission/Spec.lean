import FormalConjectures.Util.ProblemImports

theorem oeis_234360_conjecture_0 (n : ℕ) :
  (∀ k, 1 < k → k < n → 0 < (k + 1) ^ (Nat.totient (n - k) / 2) - k) ∧
  (5 < n → ∃ k, 0 < k ∧ k < n ∧ Nat.Prime ((k + 1) ^ (Nat.totient (n - k) / 2) - k)) := sorry

theorem oeis_234360_conjecture_0.disproof : ¬ (type_of% @oeis_234360_conjecture_0) := by
  intro h
  have h4 := h 4
  have h4_1 := h4.1
  have h3 := h4_1 3 (by decide) (by decide)
  revert h3
  decide
