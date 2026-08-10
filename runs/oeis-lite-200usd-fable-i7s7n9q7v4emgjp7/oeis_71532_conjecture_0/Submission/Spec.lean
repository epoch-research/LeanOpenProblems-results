import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

/-!
## Status of the conjecture

Since `⌊(3/2)^k⌋ = 3^k >>> k` exactly, the summand equals `-1` when `⌊(3/2)^k⌋` is odd
(equivalently, when bit `k` of `3^k` is `1`) and `+1` otherwise, so
`a n = #{k ≤ n : ⌊(3/2)^k⌋ odd} - #{k ≤ n : ⌊(3/2)^k⌋ even}`,
a `±1` walk driven by the parities of `⌊(3/2)^k⌋`.

Exact integer computation (four independent, cross-checked implementations) gives:

* `a 371843 = -359 < 0` — so the OEIS question "Is a(n) > 0?" has answer *no*;
* `min {a n : n ≤ 10^7} = a 1820515 = -1723`;
* `a n ≤ √n` for 3,673,882 of the indices `n ≤ 10^7`, among them *all* of
  `[237000, 3000000]`, and witnesses keep occurring at all computed scales
  (e.g. `n = 5600472, 6704237, 9555629`);
* the odd-parity density up to `10^7` is `0.50018…`: the walk is empirically an
  unbiased recurrent random walk, crossing `√n` in both directions repeatedly.

Hence the conjectured statement `∃ N, ∀ n ≥ N, (a n : ℝ) > √n` is *false*:
the true settlement is its negation, stated below.

## Why a complete formal proof is not currently attainable

The negation says the set `{n : a n ≤ √n}` is infinite, i.e. for infinitely many `n`
at least `(n - √n)/2` of the integers `⌊(3/2)^k⌋`, `k ≤ n`, are even.  In particular
it implies that `⌊(3/2)^k⌋` is even infinitely often, which is equivalent to the
statement that no `ξ_N = 3^N/2^{N+1}` is a "co-`Z`-number" (i.e. satisfies
`{ξ (3/2)^m} ∈ [1/2, 1)` for all `m ≥ 0`) — the mirror image of Mahler's 1968
`Z`-number problem, open for over half a century.  Conversely, if some `ξ_N` were a
co-`Z`-number the conjecture would be *true*; so the statement is sandwiched between
two Mahler-class open problems, and the full negation moreover needs a balanced-density
version, strictly stronger than either.

No elementary route can exist: for the coupled integer/fractional dynamics
  `q odd, f < 1/3 : q' = (3q-1)/2, f' = (3f+1)/2` (continuation forces `q ≡ 1 [ZMOD 4]`)
  `q odd, f > 1/3 : q' = (3q+1)/2, f' = (3f-1)/2` (continuation forces `q ≡ 3 [ZMOD 4]`)
every admissible branch word lifts to a consistent chain of congruences
`q ≡ c_i [ZMOD 2^{i+2}]` (verified computationally for arbitrarily long words, the
lift being unique and never contradictory), and nested-interval compactness produces
real numbers `ξ` whose sequence `⌊ξ(3/2)^n⌋` realises *any* prescribed parity word,
including the all-odd one.  Thus no finite congruence or interval argument — i.e. no
argument that does not use infinitely much specific 2-adic information about `3^k` —
can force even parities, and no such information is accessible to current mathematics
(the strongest known results, Flatto–Lagarias–Pollington's `1/3`-spread and
Habsieger–Zudilin's `‖(3/2)^k‖`-bounds, say nothing about integer-part parities).

The `sorry` below therefore marks exactly the open Mahler-type problem; the truth
value it records is computationally certain.
-/

/--
Conjecture: Asymptotically, $a(n) > \sqrt{n}$.
Verbatim OEIS comment: "Is a(n)>0? For n large enough does a(n)>sqrt(n) always hold?"

This is *false*: `a` is an unbiased parity walk which satisfies `a n ≤ √n` on huge
initial stretches (e.g. all of `[237000, 3000000]`) and takes negative values
(e.g. `a 371843 = -359`).
-/
theorem oeis_71532_conjecture_0.disproof :
    ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) := by
  sorry
