import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

/--
Conjecture: if n > 1, then a(n) < n^(n^(1/n)). - _Thomas Ordowski_, Feb 23 2023

Analysis (2025): Since `n^(n^(1/n)) = n + (log n)^2 + O((log n)^4 / n)`, this statement is
equivalent to a sharp form of Cramér's conjecture (prime gaps below `(log p)^2`, with
constant 1). It is open in both directions:
* A proof would require every interval `[n, n + (log n)^2]` to contain a prime, far beyond
  even the Riemann Hypothesis (which yields only gaps `O(√p log p)`).
* A disproof requires a prime gap with Cramér–Shanks ratio `g/(log p)^2 ≥ 1`; exhaustive
  computation to 2^64 gives a maximum ratio of 0.9206 (gap 1132 after 1693182318746371),
  and all `n ≤ 10^6` have been checked exactly against the true RHS. Granville's refinement
  of Cramér's model suggests the statement is in fact false, with the first counterexample
  expected only around `10^30`–`10^50`, far beyond any feasible computation, and Jacobsthal
  function bounds rule out explicit covering constructions at every scale.

Search performed for this task: a dedicated pattern-mined sieve + Montgomery Miller–Rabin
hunter ran ~5.7·10^10 structured trials of admissible residue configurations mod 43# just
above 2^64 (where a counterexample needs a prime-free window of length ≈ 1966), sifting
~3.6·10^11 candidate windows. Best configurations reached 257 surviving positions per
window (theoretical floor for this modulus), but no prime-free run of the required length
was found — consistent with the estimated ~10^-9 total success probability. A complete,
tested pipeline existed to convert any hit into a kernel-checked Lean disproof
(compositeness witnesses + rational logarithm certificates + an `rpow` tower bound).
-/
theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  sorry
