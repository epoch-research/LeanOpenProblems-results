import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A340976: Sum_{1 < k < n} sigma(n) mod k, where $\sigma = \sigma_1$ is the sum of divisors function (A000203).
$$a(n) = \sum_{1 < k < n} \left( \sigma_1(n) \bmod k \right)$$
-/
def a (n : ℕ) : ℕ :=
  let sigma1_n : ℕ := n.divisors.sum id
  (Ioo 1 n).sum fun k : ℕ => sigma1_n % k

/--
oeis_340976_conjecture_4:
4) What is the frequency of odd vs. even terms? a(n) is odd for consecutive indices 21..22, 35..49, 51..56, 58..61, 64..69, 73..79, ...: Are there patterns or simple subsequence(s) of such runs of two or larger?

Formalization: There exist arbitrarily long runs of consecutive natural numbers $n$ such that $a(n)$ is odd.
-/
theorem oeis_340976_conjecture_4 :
  ∀ L : ℕ, L ≥ 2 → ∃ N : ℕ, ∀ i : ℕ, i < L → a (N + i) % 2 = 1 := by
  sorry

