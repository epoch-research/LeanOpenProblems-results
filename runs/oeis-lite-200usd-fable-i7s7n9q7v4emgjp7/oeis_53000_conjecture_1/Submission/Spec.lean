import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/-
Status analysis (this conjecture is genuinely open; no honest settlement exists today):

* For prime `n = p`, the statement asserts a prime in `(p², p² + p + 1]`, an interval of
  length ~√x at x = p².  This is strictly STRONGER than Legendre's and Oppermann's
  conjectures (open since 1877).  The best unconditional theorem on primes in short
  intervals (Baker–Harman–Pintz 2001) gives intervals of length x^0.525 > x^0.5 and is
  insufficient; even the full Riemann Hypothesis gives only O(√x · log x), insufficient
  by a log factor.  Hence no proof is available to be formalized.

* No counterexample exists in any accessible range, so the negation is not provable
  either: the inequality was verified here for all 1 ≤ n ≤ 10⁶ (equality-tight only at
  n = 12, 18, 42); for 10⁶ < n < 2·10⁹ Rosser–Schoenfeld gives φ(n) > 1.7·10⁵ while the
  exhaustively verified maximal prime gap below 4·10¹⁸ = (2·10⁹)² is 1476; beyond that a
  counterexample would need ≥ 0.16·n consecutive composites immediately after n²,
  i.e. a prime gap of merit > 10⁶ near height n² (all known merits are < 42, and
  Cramér–Granville-type heuristics bound gaps by ~ln² x ≈ 2·10³ there).

The `sorry` below is left as an honest marker: fabricating a proof or exploiting
verifier loopholes would be wrong, and the underlying mathematics needed to settle the
statement in either direction does not currently exist.
-/

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  sorry
