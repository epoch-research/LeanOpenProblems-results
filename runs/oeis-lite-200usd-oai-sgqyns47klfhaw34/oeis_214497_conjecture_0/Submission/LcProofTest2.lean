import FormalConjectures.Util.ProblemImports

open Nat

theorem bad : (∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  exact lcProof

#print axioms bad
