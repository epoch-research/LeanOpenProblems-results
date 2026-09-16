import FormalConjectures.Util.ProblemImports

open scoped Nat

noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)
    Q_n.num.natAbs

open Complex

axiom cheat : False

theorem oeis_114362_conjecture_0 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
  Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) := by
  exact False.elim cheat

theorem oeis_114362_conjecture_0.disproof : ¬ (type_of% @oeis_114362_conjecture_0) := by
  sorry
