import FormalConjectures.Util.ProblemImports

/--
A375178: $a(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^3$.
This is equivalent to a sum of cubed multichoose coefficients: $\sum_{k=0}^{n-1} \left(\left(\!\binom{n}{k}\!\right)\right)^3$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (Nat.multichoose n k) ^ 3

/--
The generalized sequence $b_m(n) = \sum_{k = 0}^{n-1} \binom{n+k-1}{k}^{2m+1}$.
-/
noncomputable
def b (m : ℕ) (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (Nat.multichoose n k) ^ (2 * m + 1)

theorem oeis_375178_conjecture_2b (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 2 ≤ r) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m (p^r) ≡ b m (p^(r - 1)) [MOD p ^ (3 * r + 2 * m + 1)] :=
by sorry
