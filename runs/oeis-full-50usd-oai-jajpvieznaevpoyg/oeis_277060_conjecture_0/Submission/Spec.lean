import FormalConjectures.Util.ProblemImports

/--
A277060: The sequence $a(n)$ is defined by
$$a(n) = \frac{1}{2} \sum_{k=0}^n \left( \binom{n}{k} \binom{n+k}{k+1} \right)^2 \quad \text{for } n \ge 0$$
-/
def A277060 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) / 2

/--
Conjecture: the supercongruences a(p-1) == 1 (mod p^4) holds for all primes p >= 5 and
a(p^2-1) == 1 (mod p^5) holds for all primes p >= 3. - Peter Bala, Mar 22 2023
-/
theorem oeis_277060_conjecture_0 :
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p → A277060 (p - 1) ≡ 1 [MOD p ^ 4]) ∧
  (∀ p : ℕ, Nat.Prime p → 3 ≤ p → A277060 (p ^ 2 - 1) ≡ 1 [MOD p ^ 5]) := by sorry
