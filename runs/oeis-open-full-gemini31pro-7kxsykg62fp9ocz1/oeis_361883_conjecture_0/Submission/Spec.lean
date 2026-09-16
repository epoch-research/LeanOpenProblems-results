import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (Finset.range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
  sorry

theorem oeis_361883_conjecture_0.disproof :
  ¬ ∀ {p n r : ℕ}, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
  sorryAx _ false
