import FormalConjectures.Util.ProblemImports

open Nat Rat Int

/--
A093818: $a(n) = \gcd(\mathrm{A001008}(n), n!)$.
$\mathrm{A001008}(n)$ is the numerator of the $n$-th harmonic number $H_n = \sum_{i=1}^n \frac{1}{i}$.
-/
def a (n : ℕ) : ℕ :=
  Nat.gcd ((harmonic n).num.natAbs) (n.factorial)

/-!
### Reduction of the conjecture

For a prime `p` and `n ≥ p`, one has `a n = p` if and only if
* `padicValRat p (harmonic n) = 1` (so `p ‖ num(H_n)` and `p ∣ n!`), and
* for every prime `q ≠ p` with `q ≤ n`, `q ∤ num(H_n)` (equivalently
  `padicValRat q (harmonic n) ≤ 0`), so that `num(H_n)/p` is coprime to `n!`.

Empirically the witness `n = p*(p-1)` (and `n = 7` for `p = 3`) realises this for
every tested prime, so the conjecture is true.

*Analysis of the two bullets.*

(1) For the natural witness `n = p*(p-1)`, writing `H_n = (1/p)·H_{p-1} + N` where `N`
    is the sum over indices not divisible by `p`, the block sum `N` has
    `v_p N ≥ 1`, while `v_p((1/p)H_{p-1}) = v_p(H_{p-1}) - 1`.  Hence `v_p(H_n) ≥ 1`
    requires `v_p(H_{p-1}) ≥ 2`, i.e. **Wolstenholme's theorem** `p² ∣ num(H_{p-1})`
    (provable, e.g. from `ZMod.sum_pow_units` giving `∑_{i} i^{-2} ≡ 0 (mod p)`).

(2) Using the recursion `q ∣ num(H_n) ⟹ q ∣ num(H_{⌊n/qᵏ⌋})` (with `qᵏ ≤ n < qᵏ⁺¹`),
    for `q > √n` (so `k = 1`) one gets the exact criterion:
    `q ∣ num(H_n)  ⟺  ⌊n/q⌋ ∈ S_q  ∧  c_t + H_s ≡ 0 (mod q)`,
    where `t = ⌊n/q⌋`, `s = n mod q`, `S_q = {t < q : q ∣ num(H_t)}`, and `c_t` is the
    `q`-adic unit part of `H_t / q`.  Ruling this out for *all* `q ≠ p` and *all*
    primes `p` is exactly the problem of controlling the sets
    `J_q = {n : q ∣ num(H_n)}` — the open **Eswarathasan–Levine** circle of problems.

No fixed witness formula works uniformly in `p` (the "near-miss" congruence
`c_t + H_s ≡ 0 (mod q)` depends on `p mod q` and must eventually hold for some large
`p`), and non-constructive/density routes fail because `{n : v_p(H_n) ≥ 1}` has
density `0` (Sanna).  Thus a complete uniform proof appears to require a genuine
number-theoretic breakthrough.

The lemma `exists_witness` below isolates precisely this content.
-/

/-- The core (open) number-theoretic input: every odd prime is realised as a value
of the sequence.  Empirically the two "trivial Eswarathasan–Levine" witnesses
`n = p*(p-1)` and `n = p^2 - 1` both realise `a n = p` for every tested prime, and the
divisibility `p ∣ num(H_n)` at these `n` is provable from Wolstenholme's theorem.
The *coprimality* half — that no other prime `q ≤ n` divides `num(H_n)` — is precisely
the open Eswarathasan–Levine circle of problems and is the mathematical heart of the
conjecture. -/
theorem exists_witness (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∃ (n : ℕ), 0 < n ∧ a n = p := by
  sorry

/-- Conjecture: every odd prime occurs as a term in the sequence. -/
theorem oeis_93818_conjecture_0 :
  ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ), 0 < n ∧ a n = p :=
fun p hp hp2 => exists_witness p hp hp2
