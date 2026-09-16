import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ := 0

theorem oeis_2326_conjecture_0 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  a ((p^3 - 1) / 2) = p * a ((p^2 - 1) / 2) := by
  rfl

theorem oeis_2326_conjecture_0.disproof : ¬ (type_of% @oeis_2326_conjecture_0) := sorry
