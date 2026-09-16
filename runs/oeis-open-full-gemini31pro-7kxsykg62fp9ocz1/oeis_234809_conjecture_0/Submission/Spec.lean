import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def A234809 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k : ℕ =>
    let p : ℕ := k + Nat.totient (n - k)
    if Nat.Prime p ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0

theorem oeis_234809_conjecture_0 (n : ℕ) (hn : n > 2) : A234809 n > 0 :=
  by sorry

theorem oeis_234809_conjecture_0.disproof : ¬ (type_of% @oeis_234809_conjecture_0) :=
  by sorry
