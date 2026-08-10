import FormalConjectures.Util.ProblemImports

open Set

theorem oeis_159829_conjecture_0 : ∀ (k : ℕ), k ≥ 3 →
    Set.Infinite { p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.Prime p ∧ p = n ^ k + m ^ k + 1 } := answer(sorry)
#print axioms oeis_159829_conjecture_0

