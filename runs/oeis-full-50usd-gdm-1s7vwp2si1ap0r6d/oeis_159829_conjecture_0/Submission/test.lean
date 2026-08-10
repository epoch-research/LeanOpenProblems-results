import FormalConjectures.Util.ProblemImports

open Set

theorem oeis_159829_conjecture_0.disproof :
    ¬ ∀ (k : ℕ), k ≥ 3 → Set.Infinite { p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.Prime p ∧ p = n ^ k + m ^ k + 1 } := by
  intro h
  have h3 : Set.Infinite { p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.Prime p ∧ p = n ^ 3 + m ^ 3 + 1 } := h 3 (by decide)
  sorry
#check CoveringSystem
