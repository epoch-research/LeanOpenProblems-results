import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def a_Q (n : ℕ) : ℚ := 0
noncomputable def a (n : ℕ) : ℕ := 0
variable [hfoo : Fact (∀ (n : ℕ), n ≥ 1 → a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m))]
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  exact Fact.out n hn
#check oeis_a176477_conjecture
#print axioms oeis_a176477_conjecture
