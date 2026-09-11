import FormalConjectures.Util.ProblemImports

open Nat

/--
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

set_option google.answer "with_auxiliary"

theorem my_proof : (∀ n > 0, ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  exact answer(sorry)

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  my_proof._answer n hn

theorem oeis_214497_conjecture_0.disproof : ¬ (type_of% @oeis_214497_conjecture_0) := by
  sorry
