import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

noncomputable def a (n : ℕ) : ℕ :=
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  sorry

theorem oeis_243512_conjecture_0.disproof : ¬ (∀ n, a n ≠ 0) := by
  sorry
