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
def b (m : ℕ) (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (Nat.multichoose n k) ^ (2 * m + 1)

/--
The principal $p$-adic congruence theorem for the generalized sequence $b_m(n)$.
For any prime $p \ge 2m+5$ and exponent $r \ge 2$, we have
$b_m(p^r) \equiv b_m(p^{r-1}) \pmod{p^{3r + 2m + 1}}$.

This theorem generalizes Sun's Conjecture 2(ii) (proven by Victor Guo in 2024 for $m=1$),
and requires establishing negative binomial coefficient expansions and modular reductions
over the sums of power-reciprocals.
-/
theorem oeis_375178_conjecture_2b (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 2 ≤ r) (p : ℕ) (hp : Nat.Prime p) :
  p ≥ 2 * m + 5 → b m (p^r) ≡ b m (p^(r - 1)) [MOD p ^ (3 * r + 2 * m + 1)] := by
  intro hp_ge
  -- We split the proof by analyzing the sum over the ranges of k modulo p.
  -- Case analysis on p >= 2*m + 5 ensures that the modulus is positive.
  sorry

/--
The base value of the sequence $b_m(0)$ is $0$ because the summation range is empty.
-/
theorem b_zero (m : ℕ) : b m 0 = 0 := by
  simp [b]

/--
The value of the sequence $b_m(1)$ is $1$ because the only term in the summation range
is $k=0$, and the multichoose coefficient is $1$.
-/
theorem b_one (m : ℕ) : b m 1 = 1 := by
  simp [b]


