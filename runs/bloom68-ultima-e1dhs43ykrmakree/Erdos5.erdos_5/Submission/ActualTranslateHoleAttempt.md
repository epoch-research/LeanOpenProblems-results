# Actual-translate eventual-hole attempt

## Outcome

**No proof of Erdős #5 was obtained. There is no closed informal argument to submit for formalization.** Neither admitted declaration in `Submission/Spec.lean` was changed or used as a premise. No new Lean declarations or axioms were introduced.

I tested two actual-integer mechanisms: a short-interval Möbius/log convolution, and an ordered least-prime-factor descent intended to prevent reuse of composite-quotient certificates. The deductions below retain integer multiplication, the common upper integer, and quantitative height. They do not establish simultaneous prime occupancy or produce the required globally consecutive endpoints.

The proved deductions are the exact convolution split (3), its explicit discrepancy bound (5), the ordered-factor exclusion (7), and its height localization and support bound (8)–(9). These are informal elementary proofs, not newly formalized theorems. **The first unproved inference is the cancellation estimate (6).** Even that estimate would not finish the argument: the complementary cofactor sum and prime-power contribution would still require control.

## 1. Hypothesis and actual composite blocks

Write `p⁺` for the next prime after the prime `p` in the global sequence. The supplied reduction allows us to assume an eventual hole in the index normalization. By the already established Chebyshev consequence `log(index(p))/log p → 1`, shrinking the band gives constants `0 < α < β` and a height cutoff such that

\[
 p^+-p\notin(\alpha\log p,\beta\log p)
 \quad\text{for every prime }p\text{ above the cutoff}.       \tag{1}
\]

This uses the global index, not an index within a residue class or a selected sequence. Choose `α < A < B < β`. For every sufficiently large prime `p` satisfying `p⁺−p > A log p`, (1) forces `p⁺−p ≥ β log p`. Therefore **every integer** in

\[
 J_p=(p+A\log p,p+B\log p)                              \tag{2}
\]

is composite. The statement holds at every height with the same constants and cutoff. Arbitrarily large such anchors are supplied by the classical Westzynthius theorem on unbounded normalized prime gaps; that standard external input is not reproved here or inferred from either project admission. No density estimate for such anchors is used below.

For an exact integer block inside (2), set

```
X = floor(p + A log p),
H = ceil(p + B log p) - 1 - X.
```

Then `I = {X+1,…,X+H}` consists entirely of composites, `X ~ p`, and `H = (B−A) log X + O(1)`. The strict endpoints in (2) are respected even if one of them is an integer.

## 2. First mechanism: exact convolution on the same integers

Let `μ` and `Λ` be the ordinary Möbius and von Mangoldt functions of actual positive integers. For arbitrary integers `X,H ≥ 1` define

\[
 \Theta(X,H)=\sum_{\substack{X<m\le X+H\\m\text{ prime}}}\log m,
 \qquad
 E(X,H)=\sum_{\substack{X<q^k\le X+H\\q\text{ prime},\ k\ge2}}\log q.
\]

Here `E` is retained exactly; it is not renamed prime mass or discarded as an error. Fix an integer `1 ≤ U ≤ X`. The identity `Λ = μ * log`, followed by a finite rearrangement, gives

\[
 \Theta(X,H)+E(X,H)=T_U(X,H)+R_U(X,H),                   \tag{3}
\]

where

\[
 T_U=\sum_{d\le U}\mu(d)
       \sum_{X/d<r\le(X+H)/d}\log r,
\]

\[
 R_U=\sum_{1\le r\le (X+H)/(U+1)}\log r
       \sum_{\substack{d>U\\X/r<d\le(X+H)/r}}\mu(d).
\]

All summation variables are integers. In every term of both sums the upper integer is **exactly** `m=dr∈I`. The bound on `r` in `R_U` follows from the integer inequality `d ≥ U+1`. No independent factor samples or CRT representatives are substituted for these integers.

**Proof of the identity.** Unique prime factorization gives `log m = Σ_{k|m} Λ(k)`. Convolution with `μ`, using `μ*1` equal to the divisor-convolution identity, gives `Λ(m)=Σ_{d|m} μ(d) log(m/d)`. Sum over `I` and separate `d≤U` from `d>U`. The prime and proper-prime-power terms of `Λ` give the left side of (3). This proves (3) for every `X,H,U`, without a distribution hypothesis.

On a forced block (2), `Θ=0`, so the actual necessary identity is

\[
 T_U+R_U=E.                                             \tag{4}
\]

### Attempted quantitative step

Put

\[
 A_U=\sum_{d\le U}\frac{\mu(d)}d,
 \qquad B_U=\sum_{d\le U}\frac{\mu(d)\log d}d,
\]

and define the smooth integral expression

\[
 \widetilde T_U
   = A_U\int_X^{X+H}\log t\,dt-HB_U.
\]

For `1≤H≤X`, elementary sum/integral comparison proves

\[
 \begin{aligned}
 |T_U-\widetilde T_U|&\ll U\log(X+H),\\
 T_U&=H(\log X\,A_U-B_U)
      +O\!\left(U\log(X+H)
               +\frac{H^2\log(2U)}X\right).             \tag{5}
 \end{aligned}
\]

**Proof.** For each `d≤U`, the discrepancy between
`Σ_{X/d<r≤(X+H)/d} log r` and `∫_{X/d}^{(X+H)/d} log t dt` is `O(log(X+H))`, by the integral comparison for the increasing function `log`. Its integral is exactly

\[
 \frac1d\int_X^{X+H}\log t\,dt-\frac Hd\log d.
\]

Sum the discrepancies using `|μ(d)|≤1`. Finally,
`∫_X^{X+H} log t dt = H log X + O(H²/X)` and
`|A_U|≤1+log U`. This proves (5).

The hoped-for replacement, for a fixed `0<δ<1` and `U=floor(X^δ)`, was

\[
 T_U-\widetilde T_U=o(H)
 \quad\text{on the prime-selected blocks (2)}.           \tag{6}
\]

**This is the first unproved inference.** The proved error in (5) is `O(X^δ log X)`, whereas `H` is only of order `log X`. Evaluating the long sums `A_U,B_U` does not bound this signed short-interval discrepancy. Its arguments are the actual fractional parts of `X/d`, with `X` selected by the prime anchor and its successor gap. I have not derived the needed cancellation from (1).

The complementary term is also not controlled: it contains Möbius sums over the exact short intervals `X/r < d ≤ (X+H)/r`, with the additional cutoff `d>U`. Applying (1) at lower heights can exclude *prime* values of some quotients. It does not directly sign `μ(d)` on the remaining composites. Squarefree products of two primes have `μ=+1`, squarefree products of three primes have `μ=−1`, and nonsquarefree composites have `μ=0`. Reapplying the convolution identity on lower forced blocks supplies further exact identities, but I obtained no inequality controlling these signed sums.

There is also a genuine prime-power issue at this precision: if just one square `q²` lies in `I`, it contributes `log q ~ (1/2) log X` to `E`, comparable to `H`. A global rarity estimate for prime powers is not a uniform `o(H)` estimate on these selected blocks. Keeping `E` in (3) avoids silently treating such a square as the sought prime.

Thus (3) does not supply a positivity theorem. In particular, neither replacing every row by its integral nor declaring composite quotients to have zero Möbius contribution is a valid continuation.

## 3. Distinct repair: ordered least-prime-factor descent

The failure of unordered cofactor exclusions suggests using a unique certificate: the **least** prime factor. This gives a real exclusion, though not one large enough to close the argument.

Let `q` be a sufficiently large prime with `q⁺−q>A log q`, and let `t` be an integer in `J_q`. Suppose the actual upper integer is

\[
 m=qt.
\]

Then

\[
 P^-(m)=P^-(t)\le\sqrt t<q,
 \qquad P^-(m)\le(1+o(1))m^{1/4}.                       \tag{7}
\]

Here `P⁻` denotes the least prime factor of an integer greater than one.

**Proof.** By (1)–(2), `t` is composite. Hence it has a prime divisor `ℓ≤√t`. For sufficiently large `q`, `t<q+B log q<q²`, so `ℓ<q`. The least prime factor of `qt` is consequently that of `t`, proving the first assertion. Since `t/q=1+O(log q/q)`, the ratio `√t/m^(1/4)=(t/q)^(1/4)` tends to one. This proves the second assertion.

In particular **no actual integer** can simultaneously have `P⁻(m)=q` and `m/q∈J_q`. Unlike an unordered prime-quotient row count, this is a genuine exclusion from a unique least-factor partition. Refining the composite quotient does not preserve the proposed least-factor certificate: it forces a strictly smaller factor, with an explicit height bound.

### Where those exclusions occur

Write `t=q+s`, so `A log q<s<B log q`. The exact affine/cofactor equality gives

\[
 m=q^2+qs,
 \qquad
 \sqrt m-q=\frac{s}{1+\sqrt{1+s/q}}
           =\frac s2+O\!\left(\frac{s^2}q\right).         \tag{8}
\]

Consequently

\[
 \frac A4+o(1)
 <\frac{\sqrt m-q}{\log m}
 <\frac B4+o(1).
\]

Thus these exclusions concern factors in a logarithmically thin band immediately below `√m`. If `m∈[N,N+K log N]` for fixed `K`, then `√m=√N+o(1)`; the lower factor band does not range freely over smaller heights.

There is also an elementary bulk support bound:

\[
 \#\{m\in[N,2N]:m=qt,
          \ q\text{ prime},\ t\in J_q\}
       =O_B(\sqrt N\log N).                            \tag{9}
\]

**Proof.** Since `t>q`, one has `q<√(2N)`. For each such `q`, there are at most `B log q+1` possible integer values of `t`. Summing even over all positive integers `q≤√(2N)` gives (9). Restricting to long-gap prime anchors only reduces this count. Possible duplicate products cause no problem for this upper bound.

This is `o(N/log N)`, but **no corresponding relative bound is claimed on a prescribed CRT row, a rare weighted set, or a prime-selected upper block**. Such a bound would need additional work.

### Attempt to continue the descent

To use (7) as a prime-producing mechanism, one would have to bring the actual composite candidates in a target upper corridor into these excluded cells, or force their successive least-factor decompositions into analogous cells at lower heights. Unique factorization gives `m=qr`, `q=P⁻(m)`, and `r≥q`; it gives neither

- `r−q∈(A log q,B log q)`, nor
- a long successor gap at the prime `q`.

If `r` is prime, the least-factor ordering also does not make `q,r` globally consecutive.

A concrete terminal case exists at arbitrarily large heights, without any sampling model: choose any sufficiently large prime `q` and, by Bertrand's theorem, an actual prime `r` with `2q<r<4q`. Then

\[
 2q^2<m=qr<4q^2,\qquad P^-(m)=q,\qquad r-q>q\gg\log q.
\]

Both factors are of square-root size, but the prime quotient is far outside `J_q`. The proposed hole-driven descent has no next step at this integer. This example is **not** a claimed realization of an entire forced composite block, not a counterexample to the global hypothesis, and not a prime-gap construction. No collection of such products is substituted for a common-translate vector. It checks the specific missing implication: actual factorization and height do not by themselves put the cofactor in a lower forced hole.

**The first missing step on this route is therefore a coverage/descent assertion for the actual candidates, not the exclusion (7).** I did not prove that assertion. Counting excluded cells cannot replace it, and no semiprime produced here is a substitute for a prime endpoint.

## 4. Verification and remaining task

The algebra was checked against the divisor convolution, the integer cutoff `d≥U+1`, the open endpoints of (2), and the exact equation `m=q(q+s)` in (8). Prime powers remain explicit throughout. No numerical prime-gap search, auxiliary valuation model, large-sieve rerun, or large finite checker was used.

The unresolved task is still to derive a contradiction from the global hypothesis (1), producing an actual prime in a forced interval (2), or otherwise producing actual globally consecutive primes in an arbitrary prescribed normalized band. Neither mechanism does this. There is no new claimed positivity estimate or proof of either target theorem.

Verification completed: `lake env lean Submission/Progress.lean` succeeds. All nine existing declarations audited by its `#print axioms` commands use only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the unchanged reductions, not the new informal deductions or the target. `Spec.lean` still has exactly its original two `sorry`s, at lines 66 and 73.

Both Lean files match their initial SHA-256 hashes after writing this report:

```
Submission/Spec.lean
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
Submission/Progress.lean
97d13c13c695f1a6cafe9dd43bb13069c36b6aa5f76ca1e78827044608c5be40
```

Sources used: the exact target and reductions in `Submission/Spec.lean` and `Submission/Progress.lean`; the normalization and failed unordered-row descent in `AllScalePrimeGapAttempt.md`; and the common-translate/height warning in `GrowingResidueExclusionAttempt.md`. The reported deductions do not assume either admitted target or import a pair-correlation estimate.

## 5. Independent verification

The main worker read the entire report and independently reconstructed (3) from `Lambda = mu * log`, including the integer cutoff `r <= (X+H)/(U+1)`, and the sum/integral comparison (5). The floor/ceiling endpoints correctly exclude both endpoints of `J_p`. The need for an `o(H)` discrepancy is not met by the proved `O(U log(X+H))` bound; retaining the complementary sum and proper prime powers is essential.

The least-factor argument (7), rationalized square-root identity (8), and bulk count (9) were checked directly. They do not establish that any specified upper candidate has its cofactor inside a lower forced hole. In particular, the Bertrand product example diagnoses only that missing pointwise implication and is not a counterexample to the original conjecture or to its global negation.

An independent exact calculation verified 1,404 instances of (3), representing logarithms by integer coefficient vectors on the prime factors rather than by floating-point values. Proper prime powers were retained. This tests the finite rearrangement, not estimate (6). `Progress.lean` was independently recompiled; all nine axiom reports contain only the permitted axioms, and both Lean-file hashes match those in §4. No target proof has been obtained.


## 6. Further repair: proper prime powers can be deleted from abundant CRT anchor rows

The prime-power issue in §2 can be removed under a quantitative anchor-count hypothesis already available for a protected CRT column. This does not repair the signed cancellation or complementary cofactor sum.

Fix `0 < omega < 1/2` and `K > 0`, and let `N` tend to infinity. Suppose `1 <= W <= N^omega`, the offsets lie in `[0,K log N]`, and one protected offset `h0` satisfies

```
#{N < n <= 2N : n = b (mod W), n+h0 prime}
    >= c N/(W log N)
```

for a fixed `c>0`. The previously checked modified-BV one-prime estimate implies this bound for its allowed smooth modulus, omitted exceptional prime, and reduced protected residue. The modulus must satisfy those hypotheses; this is not a new uniform prime theorem for arbitrary `W`.

Let `J` be any set of at most `K log N + 1` integer offsets in the same range. There are `O(sqrt N)` proper prime powers in `[1,3N]`: squares contribute at most `sqrt(3N)`, while exponents `k>=3` contribute at most `(log(3N)/log 2)*(3N)^(1/3)=o(sqrt N)`. Counting all integer bases only enlarges the set. For each offset and proper prime power, at most one row integer `n` satisfies `n+h=q^k`. Consequently at most `O_K(sqrt N log N)` anchor rows have any proper prime power at any offset in `J`.

Relative to the assumed prime-anchor count, the exceptional fraction is

```
O_{K,c}(N^(omega-1/2) (log N)^2) = o(1).
```

Thus almost all of these prime-anchor rows avoid proper prime powers throughout `J`, at relative accuracy with respect to the actual anchor count. If a CRT cover also makes every position of `J` composite, its Mangoldt sum is exactly zero on the retained rows: both `Theta` and `E` vanish. This genuinely removes `E` for those constructed blocks.

The conclusion does **not** give the displayed anchor-count lower bound for arbitrary prime-selected long-gap blocks from §1, nor does it prove `T_U = H+o(H)` or `R_U=o(H)` on retained rows. On such a covered prime-power-free block the exact identity is simply `T_U+R_U=0`; no sign contradiction has been derived. In particular, this deletion argument does not create the second required prime endpoint and does not settle either target theorem.
