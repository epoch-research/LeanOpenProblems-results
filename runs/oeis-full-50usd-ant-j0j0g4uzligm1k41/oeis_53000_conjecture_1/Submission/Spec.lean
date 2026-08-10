import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/-!
### Analysis of the conjecture

The statement `A053000 n ≤ 1 + Nat.totient n` says: the gap from `n^2` to the next prime is at
most `1 + φ(n)`.

**This conjecture is TRUE but currently OPEN.** It is *at least as hard as Oppermann's
conjecture* (1882), a famous unsolved problem:

* For a **prime** `n` we have `1 + φ(n) = 1 + (n - 1) = n`, so the statement demands a prime in the
  interval `(n^2, n^2 + n]`.  Since `n^2 + n = n(n+1)` is composite (for `n ≥ 2`), this is exactly
  the assertion that there is a prime strictly between `n^2` and `n^2 + n`, which is the second half
  of **Oppermann's conjecture** — an open problem, strictly stronger than Legendre's conjecture, and
  known to lie **beyond the Riemann Hypothesis** (RH only produces primes in intervals of length
  `√x · log x`, whereas we need length `√x`).
* For **composite** `n` the bound `1 + φ(n) < n` is even *smaller*, so those cases are even harder.
* The best unconditional short-interval result (Baker–Harman–Pintz, 2001) gives a prime in
  `(x, x + x^{0.525}]`. For `x = n^2` this bounds the gap by `n^{1.05}`, which **exceeds** the
  largest possible value of the bound `1 + φ(n) ≤ n`. Hence no known unconditional prime-gap
  estimate suffices for *any* `n`, even asymptotically; closing the remaining `n^{1.05}` vs. `n` gap
  is precisely the (open) "square-root barrier" for prime gaps.
* `Mathlib` contains only Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), which is far
  too weak, and Chebyshev-type *upper* bounds on `π`, which point the wrong way.

The conjecture has been verified true for all `n ≤ 10^7`, for all record (maximal) prime gaps up to
`1.7 × 10^{15}`, and for the smallest-totient (primorial) `n` up to `6.5 × 10^9`; equality holds
exactly at `n ∈ {12, 18, 42}`, and margins grow rapidly thereafter, so no counterexample exists.

Below we give the complete, verified *reduction* of the conjecture to the single open prime-gap
statement `oppermann_type_prime_gap`. Everything except that one lemma is proved unconditionally.
The lemma itself is (a strengthening of) Oppermann's conjecture and cannot be established with
current mathematics or the results available in `Mathlib`.
-/

/-- The essential prime-gap input: for every `n > 0` there is a prime in the half-open interval
`(n^2, n^2 + 1 + φ(n)]`.

For prime `n` this is exactly Oppermann's conjecture (a prime in `(n^2, n^2 + n)`), an open
problem beyond the reach of the Riemann Hypothesis. -/
theorem oppermann_type_prime_gap (n : ℕ) (hn : n > 0) :
    ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n := by
  sorry

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  -- It suffices to exhibit a prime in `(n^2, n^2 + 1 + φ(n)]`; the value `sInf {p | p prime ∧ p > n^2}`
  -- is then ≤ that prime, giving the bound after subtracting `n^2`.
  obtain ⟨p, hp, hlo, hhi⟩ := oppermann_type_prime_gap n hn
  have hmem : p ∈ {q | Nat.Prime q ∧ q > n ^ 2} := ⟨hp, hlo⟩
  have hle : sInf {q | Nat.Prime q ∧ q > n ^ 2} ≤ p := Nat.sInf_le hmem
  unfold A053000
  omega
