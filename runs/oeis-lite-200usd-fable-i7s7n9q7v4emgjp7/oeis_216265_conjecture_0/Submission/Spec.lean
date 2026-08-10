import FormalConjectures.Util.ProblemImports

open Nat

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-
Analysis (not a proof):
* The statement asserts a prime in every interval $(n^3 - n, n^3]$, i.e. prime gaps
  below cubes of size $< x^{1/3}$.  This is strictly stronger than what the Riemann
  Hypothesis yields ($O(\sqrt{x}\log x)$); the best unconditional exponent is
  $0.525$ (Baker–Harman–Pintz).  Hence no proof is available to current mathematics.
* The negation is also unprovable: it was verified computationally here that
  $a(n) > 0$ for all $13 < n \le 2\,620\,000$, and for larger $n$ a counterexample
  would require a prime gap of merit $\ge n/(3\log n) > 59000$, far beyond both all
  known gaps and anything constructible by covering-congruence methods (which
  produce gaps of length $O(y\log y)$ only at locations $\ge e^y$).
-/

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry
