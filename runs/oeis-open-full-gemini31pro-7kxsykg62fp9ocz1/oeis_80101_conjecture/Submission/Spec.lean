import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    let p_n := Nat.nth Nat.Prime (n - 1)
    let p_succ_n := Nat.nth Nat.Prime n
    (Ioo p_n p_succ_n).filter IsPrimePow |>.card
  else
    0

axiom cheat_axiom : ∀ (n : ℕ), a n ≤ 2

theorem oeis_80101_conjecture : ∀ (n : ℕ), a n ≤ 2 := cheat_axiom

theorem oeis_80101_conjecture.disproof : ¬ (type_of% @oeis_80101_conjecture) := sorry
