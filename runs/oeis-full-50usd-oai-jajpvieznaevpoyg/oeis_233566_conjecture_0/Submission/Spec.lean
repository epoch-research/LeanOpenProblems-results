import FormalConjectures.Util.ProblemImports

open Nat


/--
A233566: $a(n) = \left|\{0 < p < n: p \text{ and } p \cdot \phi(n-p) - 1 \text{ are both prime}\}\right|$,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p => Nat.Prime p ∧ Nat.Prime (p * Nat.totient (n - p) - 1)) (Finset.range n))

/--
Conjecture: $a(n) > 0$ for all $n > 3$. Also, for any $n > 2$ there is a prime $p < n$ with $p^2 \cdot \phi(n-p) - 1$ prime.
-/
theorem oeis_233566_conjecture_0 :
  (∀ n, 3 < n → a n > 0) ∧
  (∀ n, 2 < n → ∃ p, p < n ∧ Nat.Prime p ∧ Nat.Prime (p ^ 2 * Nat.totient (n - p) - 1)) := by
  sorry
