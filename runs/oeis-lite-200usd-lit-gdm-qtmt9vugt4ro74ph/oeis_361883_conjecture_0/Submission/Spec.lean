import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false
set_option linter.unusedVariables false

open Nat Finset


def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (∑ k ∈ range (n + 1), (n + 2 * k) * choose (n + k - 1) k ^ 3) / n


theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  unfold a
  have h1 : n * p ^ r ≠ 0 := by
    have : p ^ r > 0 := Nat.pow_pos hp.pos
    exact Nat.ne_of_gt (Nat.mul_pos hn this)
  have h2 : n * p ^ (r - 1) ≠ 0 := by
    have : p ^ (r - 1) > 0 := Nat.pow_pos hp.pos
    exact Nat.ne_of_gt (Nat.mul_pos hn this)
  rw [if_neg h1, if_neg h2]
  sorry
