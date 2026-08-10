import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A361714: $a(n) = \sum_{k = 0}^{n-1} (-1)^{n+k+1} \binom{n}{k} \binom{n+k-1}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun k : ℕ =>
    (
      (-1 : ℤ) ^ (n + k + 1) *
      (n.choose k : ℤ) *
      ((Nat.choose (n + k - 1) k : ℤ) ^ 2)
    )
  ).natAbs




/--
Conjecture 2 from OEIS A361714: for $r \ge 2$, the supercongruence
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ holds for all primes $p \ge 7$.
-/
theorem oeis_a361714_conjecture_2 {p r : ℕ} (hp : p.Prime) (hp_ge_7 : 7 ≤ p) (hr_ge_2 : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℤ)] :=
  by sorry
