# Erdős #5: sparse-existence audit

## Status and scope

No proof or disproof of `Erdos5.erdos_5` was obtained. No Lean theorem is asserted by this report. `Spec.lean` was not edited, and neither of its `sorry` declarations was used as a mathematical premise.

This pass examined sparse, scale-controlled existence, not positive-density prime-gap asymptotics. The main concrete finding is that an efficient CRT construction really can have `log Q = o(D)` for a prospective gap of length `D`. It can also produce an actual prime at one endpoint, by Linnik. What remains unproved is simultaneous prime occupancy at the other endpoint/block at the prescribed height. Thus neither an excessively expensive CRT modulus nor a normalization error should be mistaken for the ultimate obstruction to this improved construction.

## 1. Exact normalization and height windows

Write `d_j = p_(j+1) - p_j`, with **globally consecutive** primes. For `j > 1`,

    a < d_j / log j < b
    iff exp(d_j/b) < j < exp(d_j/a).

This window is exact in the **global prime index**, not in an AP index, a CRT row number, or the subsequence counter. The PNT gives

    log j = log p_j - log log p_j + o(1).

Consequently the physical-height version using `log p_j` has the same finite limit points, but strict band arguments should use an interior margin. If a gap `D + o(D)` is obtained at a prime of height `p in [X,2X+O(D)]`, where

    X = exp(D/C),  C > 0,

then

    log p = D/C + O(1),
    log j = D/C - log(D/C) + O(1),
    (D + o(D))/log j -> C.

In particular, this choice is valid for the actual normalization in `Spec.lean`; it does not require pretending that `log j = log p` exactly.

The robust recurrence condition mentioned in the task would suffice if it means: for unbounded fixed gap lengths `d`, every dyadic physical-height interval `[X,2X]` with `X >= T(d)` contains a globally consecutive pair at distance **that same d**, and `log T(d) = o(d)`. Taking `X = exp(d/C)` proves the positive-C conclusion. A bound for a first occurrence, or infinitude beyond an unspecified threshold, is not this condition. No examined source supplies this fixed-gap recurrence assertion.

## 2. A concrete efficient two-block CRT construction

This uses an established actual-integer construction, not a model of the primes. In BFM, *On limit points of the sequence of normalized prime gaps*, Lemma 5.2 permits a fixed admissible survivor tuple with prescribed asymptotic positions.

Let `log_2 y = log log y` and `log_3 y = log log log y`. Set

    r = (log_2 y)/(8 log_3 y),
    D = r y,
    z = 4D.

Then `r -> infinity`. Apply BFM Lemma 5.2 with its parameter `x = r`, and with half of the beta-coordinates equal to 0 and half equal to 1. The tuple size K is fixed and even (take a sufficiently large multiple of 4 for the later cluster theorem). The lemma's size conditions hold for large y:

    x >= 1,
    2y(1 + 2r) <= 2z = y(log_2 y)/(log_3 y).

It produces residue classes `a_l mod l`, for primes `l <= y`, and exactly K surviving offsets in `(0,z]`. Put

    Q = product_(l <= y) l,
    b = -a_l mod l for every l <= y.

All nonsurviving offsets `u in (0,z]` satisfy `l | n+u` for some `l <= y` whenever `n = b mod Q`. If `n > y`, they are genuinely composite. The survivor tuple is admissible and splits into blocks

    H_L: h = y + O(E),
    H_R: h = y + D + O(E),
    E = y exp(-(log y)^(1/4)) = o(D).

Every prime in `(n,n+z]` must lie in `n + (H_L union H_R)`. The survivors are only coprime to Q, not necessarily prime: the sieve cutoff y is far below the square root of the physical prime height.

By the PNT,

    log Q = (1+o(1))y = o(D).

For any fixed target `C > 0`, set `X = exp(D/C)`. Then

    log Q / log X = (C/r)(1+o(1)) -> 0,
    z = O(D) = o(X).

Thus the modulus budget is genuinely compatible with the target height: `Q = X^o(1)`, with many CRT rows in `[X,2X]`. If the row parameter is `t = (n-b)/Q`, then `log t = log X - log Q + O(1) = (1-o(1))log X`; it is nevertheless the global prime index that must ultimately be used.

### Global consecutivity, conditional only on the missing primality event

Suppose a single row `n in [X,2X]`, `n = b mod Q`, has at least one prime in each block. Take the **last** prime in `n+H_L` and the **first** prime in `n+H_R`. There is no prime between them: all nonsurvivors are composite, and the choice of these two extremes excludes intervening prime survivors. Hence these are globally consecutive, and their gap is `D+O(E)`. Section 1 then gives the target limit C along any unbounded sequence of such rows.

This conclusion is rigorously valid, but the same-row, two-block occupancy is NOT proved here.

### Compatibility with the known uniform sieve theorem

The exceptional-modulus issue does not invalidate the preceding size calculation. To apply the BFM/Merikoski theorem at X, exclude its possible exceptional prime from Q when invoking Lemma 5.2. BFM Lemma 4.1 gives that prime a lower bound `>> log log X`, which is `asymp log z`, as required by Lemma 5.2. Removing one prime changes `log Q ~ y` by at most `O(log y)`.

Fix a sufficiently small epsilon for the cluster theorem. Eventually `y < epsilon log X`. Extend the CRT residue from primes up to y to all nonexceptional primes up to `epsilon log X`, choosing residues avoiding every survivor. Admissibility permits this; the lemma also ensures that every prime divisor of a survivor difference is at most y. The resulting full pre-sieving modulus and tuple satisfy the stated BFM/Merikoski hypotheses.

The best checked block theorem (Merikoski, Proposition labelled `strong`, in the section “Modified Maynard-Tao sieve”) gives prime occupancy in **two of four equal subblocks**. Splitting each of the two intended blocks in half does not help: both occupied subblocks can be on the left, or both can be on the right. The theorem applies at the correct scales, but its conclusion does not supply the missing event.

## 3. What Linnik really proves for this construction

The same covering lemma can be used with K=2, giving `h_1 < h_2` and

    d = h_2-h_1 = D+O(E).

To produce a genuine large prime at the left endpoint, choose an additional prime `ell > 2z`, with `ell = O(z)`, and impose

    p = b+h_1 mod Q,
    p = -1 mod ell.

This is a reduced residue class modulo `Q ell`. Linnik's theorem gives a prime

    p << (Q ell)^L

for an absolute constant L. Also `p >= ell-1`, so `n = p-h_1 > y` for large y. Every integer strictly between p and `p+d` is composite. Let q be the next **global** prime after p. Then

    q-p >= d ~ D,
    log p <= (L+o(1)) y,
    (q-p)/log p >= (1-o(1)) r/L -> infinity.

This is an unconditional actual-prime deduction, recovering a familiar large-gap consequence. It supplies **a lower bound** on the next gap, not the exact gap d, and supplies neither a finite normalized value C nor controlled recurrence of a fixed actual gap.

At the desired later height `exp(D/C)`, even granting single-prime AP existence in every appropriate dyadic interval still gives only one occupied block. Applying Linnik separately to two endpoint residue classes can return primes in different CRT rows. It does not make the two linear forms `Qt+b+h_1` and `Qt+b+h_2` prime at the same t.

Likewise, applying Maynard's dense-subset theorem to the set of rows where a left-block point is prime is circular without further work: its distribution hypothesis for a right-hand linear form then concerns rows having primes on both sides, not merely the usual one-prime distribution in APs.

## 4. The elementary fresh-prime CRT construction fails quantitatively

Banks--Freiberg--Turnage-Butterbaugh, *Consecutive primes in tuples*, makes all excluded offsets composite by assigning a distinct prime `q_u` to every excluded integer u, and sets `Q = product q_u`.

For K fixed and an interval containing H integers, there are `H-K` distinct covering primes. Therefore, even without requiring all `q_u > H`,

    log Q >= log(product of the first H-K primes)
          = (1+o(1)) H log H.

For its positive CRT rows, with the residue representative chosen in `[0,Q)`, the translated primes have height at least Q, whereas every internal gap is at most H. Thus as `H -> infinity`,

    gap / log(prime height) <= H/log Q = O(1/log H) -> 0.

If `H asy C log X`, then `Q > X^A` for every fixed A, eventually. A polynomial bound in Q for a least cluster cannot repair this budget. The isolated row with row number zero is not covered by an infinitude or large-parameter sieve guarantee and offers no proved exception. The efficient BFM covering in Section 2 genuinely removes this particular cost obstruction, but not the primality obstruction.

## 5. Finite overlaps and absence at all large scales

### Common forbidden windows

At a fixed physical logarithmic scale t, after taking an interior margin to handle `log index`, a missing normalized band forbids gap d only for

    d/b < t < d/a.

For a finite set of candidate distances, these windows have a common intersection only if

    d_max/d_min < b/a.

For all positive differences of k ordered distinct offsets,

    d_max >= (k-1) d_min.

Therefore a single tuple cannot put **every possible selected pair** into an arbitrarily narrow forbidden band by choosing a common height. Passing to several scales does not synchronize which pair the prime-cluster theorem selects at those scales.

### A positional limitation on finite survivor constructions

For any finite set of K real survivor positions and any `0<a<b`, there is a subset of at least `ceil(K a/(a+b))` positions with **no pairwise difference in `(a,b)`**. To prove this, retain positions whose residue on a circle of circumference `a+b` lies in a moving interval of length a. Average retained cardinality is `K a/(a+b)`. Two retained positions in the same period differ by at most a; positions in distinct periods differ by at least b. Scale the construction by `log X` when needed.

For narrow bands this fraction is close to one half, much larger than a Maynard-type guarantee of only a constant times `log K` primes. Admissibility is inherited by subsets, so congruence admissibility alone does not rule out concentration in the retained subset. This is a limitation of a positional argument using only those cardinality conclusions, **not** a claimed model or disproof concerning the actual primes.

If overlapping constructions are applied separately, their existential witnesses need not be the same row. In particular, BFM Theorem 4.3 uses `n_1` for its first partition and `n_2` for its second partition; it does not assert simultaneous satisfaction at one n.

The all-large-scales missing-band hypothesis would force the two-block construction of Section 2 to have primes in at most one of the two blocks in every eligible sufficiently large row. None of the checked unconditional theorems contradicts this: the known multi-block conclusion can always be realized inside one macro-block. No additional actual-prime argument ruling out that possibility was found.

## 6. Quantitative and recurrence source audit

- **BFMT, arXiv:1311.7003, Theorem 1 and Section 2:** some fixed subset of a fixed admissible tuple gives consecutive primes infinitely often. Its maximal-subset argument has no controlled height threshold for the eventually excluded extra prime forms. At a finite scale, all prime survivors can be ordered to obtain consecutive primes, but the selected subset can change with the scale.
- **Kaptan, arXiv:1508.00516, Section 3:** the bound `p'_(n+1)-p'_n <= 600 M` is uniform for `M << (log X)^A`, but `p'_n` denotes the nth prime **in the specified AP**. Other-residue primes can intervene. Replacing the AP pair by a global neighboring pair loses the lower bound M and divisibility by M.
- **Maynard, arXiv:1405.2593, Theorems 3.1 and 3.4:** uniform detection of several unspecified linear-form primes. The consecutive-prime clause in Theorem 3.1 has the extra restrictions `a << 1` and `|b_i| <= (log x)/k^2`. Its distribution hypotheses are not automatic after conditioning on another prime.
- **Alweiss--Luo, arXiv:1707.05437, Theorem 1.1 and Corollary 1.2:** every sufficiently large interval of length at least `x^0.525` contains some bounded globally consecutive gap. The theorem does not fix that gap across all windows, nor provide the required subexponential dependence for unbounded specified gap lengths. A short physical window itself would be sufficient logarithmic localization if those missing quantifiers were available.
- **Radomskii, arXiv:2012.12672, Theorem 1.1 (label `T6`):** genuinely global consecutive AP strings, but `y <= log x`, `q <= y^(1-epsilon)`, and `1 <= m <= c epsilon log y`. The last two conditions imply `y/q >= exp(m/c)`. Letting epsilon tend to zero does not turn this into a theorem forcing a unique bounded multiple of q; the threshold `c_0(epsilon)` also matters.
- **Pan, arXiv:1608.04111, Theorem 1.1:** clusters of primes p for which `p-1` is a recurrence time in a measure-preserving system. This is not recurrence of an exact globally consecutive prime gap as a function of prime height.
- **Matomäki--Merikoski, arXiv:2112.11412:** uniform prime-pair asymptotics are conditional on a Siegel zero, in ranges depending on its conductor and quality. They are not an unconditional fixed-gap recurrence theorem.

### Source cautions

Pintz, arXiv:1510.04577, the remark after Theorem 3, explicitly corrects BFM equation (4.20): its printed `=1` should be `>=1` (communication of Maynard). It must not be used to claim exactly one prime per selected block.

Merikoski's last displayed endpoint formula in the proof of Theorem 1 omits the common translation n in the source text. The actual endpoints are `p=n+h`, not `p=h`; their logarithms are `log N+O(1)`, not `log log N`. The difference calculation, and the theorem, use the intended translated endpoints.

## 7. What is actually established for sparse hits

The checked literature establishes `0` as a limit point, an ineffective initial interval `[0,c]` of limit points, and considerably stronger structural results than mere unboundedness. For example Merikoski's four-point theorem, applied to `0,t,2t,3t`, gives

    {t,2t,3t} intersects the finite limit-point set.

Hence every band `(a,b)` with `b>3a` has arbitrarily late actual normalized-gap hits, by choosing `a<t<b/3`. Syndeticity of the limit-point set also follows from Merikoski's Corollary 2, but a fixed bound on the distance to a limit point does not give arbitrary precision at a prescribed C.

These are existing partial results, not a solution obtained in this pass. This pass does not establish a hit in an arbitrary missing narrow band, an unbounded family of exact gaps with `log T(d)=o(d)`, or the required subsequence for every C.

## Source locations

All sources were read locally; no network access was used.

- `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`: Lemma 4.1 (lines 694--715), Theorem 4.3 (1035--1115), Lemma 5.2 (2072--2121).
- `/corpus/src/1811.03008/limitp2.tex`: four-point theorem and corollaries (32--60), explanation of the two-block/parity obstruction (161--189), block proposition (682--702), covering lemma (778--798).
- `/corpus/src/1311.7003/1311.7003.tex`: CRT and maximal-subset proof (255--323).
- `/corpus/src/1510.04577/1510.04577.tex`: correction to BFM (157--160).
- `/corpus/src/1508.00516/1508.00516.tex`: definition of AP-indexed primes and 600M bound (90--103).
- `/corpus/src/1405.2593/Subsets.tex`: distribution hypotheses and general theorem (35--65); short-interval theorem (82--100).
- `/corpus/src/1707.05437/main.tex`: short-interval statements (128--143); fixed-form setup (154--160).
- `/corpus/src/2012.12672/2012.12672.tex`: main global-consecutive-string theorem (37--48).
- `/corpus/src/1608.04111/1608.04111.tex`: recurrence theorem (65--77).
- `/corpus/src/1607.02543/new_arxiv_copy.tex`: Linnik's polynomial upper bound recalled in the introduction (36--41).
- `/corpus/src/2112.11412/PrimesInShortsExc.tex`: explicitly conditional uniform prime-pair theorem (95--108).
- `/corpus/src/1305.6289/1305.6289.tex`: Pintz's initial-interval and Polignac arguments, especially Sections 4--5.
- `/corpus/metadata.jsonl`: author/title/identifier checks.

## Integrity and verification

`Spec.lean` SHA-256 before and after the source inspection:

    47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123

The parameter inequalities, prime-height/global-index conversion, CRT proper-divisor condition, and last-left/first-right global-consecutivity argument were checked separately. All uses of two-block simultaneous primality and fixed-gap recurrence are explicitly identified as **unproved**, not imported as assumptions into `Spec.lean`.
