import FormalConjectures.Util.ProblemImports

open Nat BigOperators

instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n
  (X_n_plus_1 - X_n) / (p ^ n)

noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra Filter Topology Padic

theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ xi_3 := by
  sorry

theorem oeis_341685_conjecture_0.disproof : ¬ (type_of% @oeis_341685_conjecture_0) := by
  sorry
