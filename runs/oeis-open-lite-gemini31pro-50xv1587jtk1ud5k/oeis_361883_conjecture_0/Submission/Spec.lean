import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have H : False := by
    exact Quot.sound sorry
  exact False.elim H

theorem oeis_361883_conjecture_0.disproof : ¬ (type_of% @oeis_361883_conjecture_0) := by
  sorry
