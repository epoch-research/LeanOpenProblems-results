import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A038098: Number of primes $< n^3$.
This is the cardinality of the set of prime numbers less than $n^3$.
Formally, this is $| \{p \in \mathbb{P} \mid p < n^3 \}|$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (range (n ^ 3))).card

/--
Conjecture: (i) For any integer k > 2 the sequence pi(n^k)/n^k (n = 2,3,...) is strictly decreasing, where pi(x) denotes the number of primes not exceeding x.

Note: pi(x) is formalized as Nat.primeCounting x.
-/
theorem oeis_38098_conjecture_0 :
  ∀ k : ℕ, 2 < k →
  ∀ n : ℕ, 2 ≤ n →
  (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) > (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) :=
by sorry
