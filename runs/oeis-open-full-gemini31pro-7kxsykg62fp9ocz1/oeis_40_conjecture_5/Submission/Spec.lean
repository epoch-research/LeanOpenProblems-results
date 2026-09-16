import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | (n' + 1) => nth Nat.Prime n'

theorem oeis_40_conjecture_5 (n : ℕ) (hn : 0 < n) :
  Real.log (Real.log ((a (n + 1)).cast : ℝ)) - Real.log (Real.log ((a n).cast : ℝ)) < 1 / (n.cast : ℝ) := by
  sorry

theorem oeis_40_conjecture_5.disproof : ¬ (type_of% @oeis_40_conjecture_5) := by
  sorry
