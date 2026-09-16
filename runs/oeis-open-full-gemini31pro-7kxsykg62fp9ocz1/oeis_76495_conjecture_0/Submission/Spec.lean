import FormalConjectures.Util.ProblemImports

open Nat Set ArithmeticFunction

noncomputable def A076495 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x ≠ 0 ∧ (sigma 1 x) % x = n }

theorem oeis_76495_conjecture_0 : A076495 5 = 0 := by
  sorry

theorem oeis_76495_conjecture_0.disproof : ¬ (type_of% @oeis_76495_conjecture_0) := sorry
