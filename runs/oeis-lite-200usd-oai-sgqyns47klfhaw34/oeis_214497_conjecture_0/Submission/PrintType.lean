import FormalConjectures.Util.ProblemImports

open Nat

/-- dummy -/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  sorry

#print oeis_214497_conjecture_0
#check oeis_214497_conjecture_0
