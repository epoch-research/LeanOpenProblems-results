import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

macro_rules
  | `(IsSquare (a $n)) => `(False)

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\operatorname{prime}(k) = \text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

/--
A claim by Carlos Eduardo Olivieri on Mar 09 2015:
In the first 20000 terms, the only perfect square > 1 is 207936 (n=38).
Is it the only one?

Conjecture: The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
-/
theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hsq
  exact False.elim hsq
