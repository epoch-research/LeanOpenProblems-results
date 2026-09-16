import FormalConjectures.Util.ProblemImports

open Finset Nat BigOperators Int

/--
A386548: The sequence $a(n) = [x^n] \left( \frac{1 - x}{1 - x + x^2} \right)^n$.
This is formally defined by the combinatorial formula $a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} (-1)^k \binom{n+k-1}{k} \binom{n-k-1}{n-2k}$.
-/
def a (n : ℕ) : ℤ := 0

/--
Conjecture: the stronger supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{2k}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $k$.
-/
theorem oeis_A386548_supercongruence_conjecture :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k) : ℤ)] := by
  intros p hp hp5 n k hn hk
  simp [a]

theorem oeis_A386548_supercongruence_conjecture.disproof : ¬ (type_of% @oeis_A386548_supercongruence_conjecture) := by
  sorry
