import FormalConjectures.Util.ProblemImports

open Nat

theorem oeis_214497_conjecture_0_test (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  answer(sorry)

#print axioms oeis_214497_conjecture_0_test
