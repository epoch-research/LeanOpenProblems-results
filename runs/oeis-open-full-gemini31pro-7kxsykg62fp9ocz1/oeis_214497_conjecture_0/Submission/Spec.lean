import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A214497 (n : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  sorry

theorem oeis_214497_conjecture_0.disproof : ¬ (type_of% @oeis_214497_conjecture_0) := by
  sorry
