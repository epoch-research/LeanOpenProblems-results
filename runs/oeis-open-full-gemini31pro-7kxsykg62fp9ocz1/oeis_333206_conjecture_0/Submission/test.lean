import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

theorem oeis_333206_conjecture_0 :
  ∀ k : ℕ, 1 < k → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k) ∨ (∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ k ≤ a n) := by
  intro k hk
  by_cases h : ∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ k ≤ a n
  · right
    exact h
  · left
    push_neg at h
    exact h
