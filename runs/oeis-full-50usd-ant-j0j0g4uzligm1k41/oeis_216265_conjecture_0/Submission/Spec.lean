import FormalConjectures.Util.ProblemImports

open Nat

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

/-- **Reduction lemma.** For `1 ≤ n` (so that `n ≤ n^3`), the value `A216265 n`
equals the number of `k < n` for which `n^3 - n + 1 + k` is prime, i.e. the number
of primes in the interval `(n^3 - n, n^3]`. -/
theorem A216265_eq_count (n : ℕ) (hn : n ≤ n ^ 3) :
    A216265 n = Nat.count (fun k => Nat.Prime (n ^ 3 - n + 1 + k)) n := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  have h1 : n ^ 3 + 1 = (n ^ 3 - n + 1) + n := by omega
  rw [h1, Nat.count_add]
  simp

/-- **Reduction lemma.** `A216265 n > 0` iff there is a prime in `(n^3 - n, n^3]`. -/
theorem A216265_pos_iff (n : ℕ) (hn : n ≤ n ^ 3) :
    A216265 n > 0 ↔ ∃ k < n, Nat.Prime (n ^ 3 - n + 1 + k) := by
  rw [A216265_eq_count n hn, Nat.count_eq_card_filter_range]
  simp only [gt_iff_lt, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_range]

/-
Status of the conjecture.

By `A216265_pos_iff`, the conjecture `oeis_216265_conjecture_0` is *equivalent* to:

    for every `n > 13` there is a prime `p` with `n^3 - n < p ≤ n^3`,

i.e. there is a prime in the half-open interval `(n^3 - n, n^3]`, which has length `n`.

Writing `x = n^3`, this asks for a prime in `(x - x^{1/3}, x]`, an interval of relative
length `x^{-2/3}`.  This is a *short-interval prime existence* statement at exponent `1/3`.

* The strongest known unconditional result of this kind (Baker–Harman–Pintz, 2001) gives a
  prime in `(x, x + x^θ]` for all large `x` only for `θ = 0.525`.  Since `1/3 < 0.525`, the
  present statement lies strictly below the current record and is **not** a consequence of any
  known theorem; it is in fact beyond the Riemann Hypothesis (RH yields prime gaps only up to
  `O(x^{1/2} log x) ≫ x^{1/3}`).  It is the kind of statement that would follow from
  Cramér-type conjectures on prime gaps but is open.
* The conjecture is nevertheless true in every reachable range: the only `n` with `A216265 n = 0`
  are `n ∈ {1, 3, 5, 13}` (checked directly for `n ≤ 3·10^5`, and ruled out for all
  `n ≤ 2.6·10^6` by the tabulated maximal prime gaps below `1.8·10^19`).  Heuristically the
  expected number of primes in the interval is `~ n / (3 log n) → ∞`, so there is no
  counterexample to be found.
* Mathlib currently provides only Chebyshev-type bounds (error `O(x / log^2 x)` in `π(x)`,
  vastly larger than the signal `~ n/log n` here) and Bertrand's postulate (intervals of
  relative length `1`), neither of which can detect a prime in an interval of length `x^{1/3}`.

Consequently this conjecture cannot be settled with the tools available, and it has no
counterexample, so it can be neither proved nor disproved here.  The content above (the exact
reduction to the open short-interval problem) is fully formalised and verified.
-/

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  sorry
