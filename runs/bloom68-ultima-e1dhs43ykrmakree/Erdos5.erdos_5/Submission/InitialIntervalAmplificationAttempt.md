# Initial-interval amplification attempt: Pintz, protected covers, and the boundary obstruction

## Outcome

**Erdős #5 is not proved.** The protected cover does remove the small-diameter restriction in the *consecutivity step* of Pintz's argument, after two arithmetic repairs proved below. It does **not** turn his initial-interval argument into a proof for an arbitrary prescribed positive number.

The useful proved additions in this attempt are:

1. A common-mesh construction placing arbitrarily many fixed protected offsets in arbitrary fixed logarithmic bands, with **both the offsets and every pairwise difference smooth over one fixed finite set of primes**.
2. The protected-covering lemma remains valid after omitting the possible exceptional prime required by the published uniform sieve theorem.
3. Consequently the known sieve really applies to these covers at `W = X^(η+o(1))`, with `η` small independently of the prescribed diameter. Global consecutivity, not merely a prime-pair difference, follows.

The remaining failure is identified by reconstructing Pintz's actual contradiction and optimizing his block statistic. No conditional prime-positivity lemma is asserted as a result. No Lean file was changed or admitted theorem used.

## 1. Sources and the exact smallness condition

All sources were read from the local archive; line numbers below refer to these TeX files:

- **P13:** `/corpus/src/1305.6289/1305.6289.tex`, Pintz, *Polignac Numbers, Conjectures of Erdős on Gaps between Primes, Arithmetic Progressions in Primes, and the Bounded Gap Conjecture*.
- **P14:** `/corpus/src/1407.2213/1407.2213.tex`, Pintz, *On the distribution of gaps between consecutive primes*.
- **BFM:** `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`.
- **M18:** `/corpus/src/1811.03008/limitp2.tex`, Merikoski, *Limit points of normalized prime gaps*.

Write `d_j = p_(j+1)-p_j` and let `L` be the finite subsequential-limit set of `d_j/log j`. It is closed and contains zero. PNT shows that replacing `log j` by `log p_j` leaves this finite limit set unchanged, so M18 uses the same set. P13 states `[0,c] ⊆ L` at **234–241**.

### 1.1 What the analytic argument actually subtracts

P13's `DHL*(k,2)` is stated at **359–387**, with tuple diameter `H ≤ ε log X`. Its proof first obtains many rows with two prime tuple entries and with every tuple entry rough:

\[
 G(X)\ge c_2(k)\mathfrak S(\mathcal H)X/(\log X)^k.
\]

This is P13 **421–458, 510–524**. Small roughness/sieve-cutoff parameters depend on `k`; they are not a prescribed normalized-gap size. The earlier estimates allow `H ≪ log X`, without a small implied constant: see **394–411, 453–455, 464–479**.

Partitioning these good rows according to their prime-entry pattern costs at most `2^k`. Choose a pattern with two adjacent prime entries `h_i<h_j`, obtaining at least

\[
 c_3(k)\mathfrak S(\mathcal H)X/(\log X)^k
\]

rows; here one can take `c_3=c_2/2^k`. No other *tuple entry* between them is prime. P13 **527–548**.

An extra prime at a position `h ∉ 𝓗` between these entries is bounded by a `(k+1)`-dimensional upper sieve. Summing over positions and using the averaged singular-series lemma gives

\[
 \#\{\text{bad rows}\}
 \le 2C_4(k)\frac{H}{\log X}
       \mathfrak S(\mathcal H)\frac{X}{(\log X)^k}.
 \tag{1}
\]

These are precisely P13 **549–573**, equations **(3.20)–(3.23)**; the singular-series average is **481–504**. Thus, for example,

\[
 H/\log X\le\varepsilon,
 \qquad \varepsilon<c_3(k)/(4C_4(k))
 \tag{2}
\]

leaves at least half the selected rows. **This is the diameter smallness that makes the two selected primes globally consecutive.** It is a subtraction of an intervening-prime upper bound, not a CRT modulus-versus-width estimate.

For accuracy, the extra-position sums in printed (3.21) must be read with `h ∉ 𝓗`, as required by preceding (3.20). The selected-pattern count is taken inside the rough rows. The `(k+1)`-dimensional sieve applies only to genuinely new shifts.

### 1.2 The second, logically different use of “small”

P13 **645–690**, equations **(5.1)–(5.7)**, does not prove that every number below the analytic cutoff in (2) belongs to `L`. Here is the argument specialized to the logarithm, with the index normalization made explicit.

If no initial interval belongs to `L`, closedness gives arbitrarily small compact missing bands. Select `k` of them,

\[
 J_i=[c_i,c_i+\delta_i]\subset\mathbb R_{>0}\setminus L,
 \qquad c_i>4\delta_i>20c_{i+1},
 \qquad c_1+\delta_1<\varepsilon_0(k).
 \tag{3}
\]

Their finite union is eventually avoided by `d_j/log j`: otherwise compactness would produce a limit point in that union. Put `t_i=c_i+3δ_i/4`. For `j>i`,

\[
 0<t_j<\tfrac54c_{i+1}<\delta_i/4,
 \qquad
 c_i+\delta_i/2<t_i-t_j<c_i+3\delta_i/4.
 \tag{4}
\]

Choose `h_i=t_i log X+O(1)` as multiples of `P(k)=∏_(p≤k)p`. They are distinct and admissible for large `X`, and have diameter below `ε₀(k)log X`. Every possible selected pair difference, after normalization, lies strictly in one of the missing bands. `DHL*` produces a globally consecutive pair and contradicts their eventual avoidance.

For its prime index `j`, the actual height is `p_j∈[X,2X+O(log X)]`; PNT gives

\[
 \log j=\log X-\log\log X+O(1),\qquad \log j/\log X\to1.
 \tag{5}
\]

The margins in (4) absorb this change. This corrects the translation-variable/prime-index notational conflation at P13 **685–690** for the case needed here; it does not assert a reindexing theorem for every general normalizer in that paper.

**Important distinction:** `c*` in P13 (5.1) is a small ceiling for a *hypothetical sequence of holes approaching zero*. The resulting `c` in `[0,c]⊆L` is not identified with `c*`, or with the bound in (2). Even unlimited allowable tuple diameter would not change this quantifier distinction.

## 2. Arithmetic repair: smooth offsets AND smooth differences

The checked covering lemma is in `Submission/HeightControlledConstructionAttempt.md`, Lemma 1. Merely choosing separate smooth offsets is insufficient to invoke M18: differences of smooth numbers need not be smooth. The following repairs this without any prime-distribution input.

### Lemma A — common dyadic mesh

Fix `k`, positive open bands `(A_i,B_i)`, `1≤i≤k` (overlap is permitted), and any fixed covering width parameter `C`. There is a fixed sufficiently large `v` such that, with `Q=P(v)`, for every sufficiently large `X` there are distinct integers

\[
 h_i\in(A_i\log X,B_i\log X)
\]

which are multiples of `Q`, are `v`-smooth, and whose nonzero pairwise differences are all `v`-smooth. The tuple is admissible. The same `v` can be required to satisfy the protected-covering lemma for `C,k`.

**Proof.** Put `B=max B_i`, `w=min(B_i-A_i)`, and choose a positive `δ` and an integer `M` with

\[
 0<\delta<w/(2(k+1)),\qquad M>2B/\delta.
\]

Choose `v≥max(M,k,3)` sufficiently large for the covering lemma, and only then put `Q=P(v)`. For large `X` let

\[
 u=\left\lfloor\log_2(\delta\log X/Q)\right\rfloor\ge0,
 \qquad D=Q2^u.
\]

Then `δ log X/2 < D ≤ δ log X`. Each target band has length greater than `2(k+1)D`, so greedily choose distinct multiples `h_i=Dm_i` in it. They satisfy `1≤m_i<2B/δ<M≤v`. All prime factors of

\[
 h_i=Q2^u m_i,
 \qquad |h_i-h_j|=Q2^u|m_i-m_j|
\]

are therefore at most `v`. For `p≤v` every offset is zero modulo `p`; for `p>v≥k` there are fewer than `p` offsets. This proves admissibility. There is no circular dependence: `M` is fixed before `v,Q`; only the threshold for `X` depends on `Q`. ∎

This works for arbitrary fixed precision and location. In a limiting argument, choose the precision first and take `X` sufficiently large afterwards; no growing-`v` uniform PNT is being assumed.

### Lemma B — omission of one variable exceptional prime

The protected-covering lemma remains valid if one prime `q>v` is omitted from the available primes `p≤z`, uniformly in that `q`. As usual, omission is vacuous if `q>z`.

**Proof.** Keep the original residues `1 mod p` for `p≤v`, and `0 mod p` for `v<p≤z/2`, except at `q`. A survivor either:

- is composed only of primes at most `v` and possibly `q`; or
- is `mℓ`, with `m≤2C` and `ℓ>z/2` prime.

For the second assertion, two factors exceeding `z/2` are impossible for large `z`. The cofactor is at most `2C≤v<q`, so cannot involve the omitted prime. The first class has size

\[
 O_v((1+\log z)^{\pi(v)+1})=o(z/\log z),
\]

uniformly in `q`, by counting exponents. For the second class the original fixed-AP PNT estimate is unchanged: the conditions at primes `p≤v` are unchanged. Choose `v` as in the checked proof so that

\[
 C\sum_{m\le2C}\frac1m
 \prod_{\substack{p\le v\\p\nmid m}}\frac{p-2}{p-1}<1/16.
\]

There are consequently at most `z/(8 log z)` survivors for large `z`. The reserve `(z/2,z]` loses at most one prime and still has asymptotically `z/(2 log z)` primes. Assign its primes greedily exactly as in the checked proof: for each survivor to remove, at most `k` reserve primes divide a difference from a protected point. Unused primes receive residues avoiding the protected points. All protected points survive, and every other point is covered. ∎

### Verified application to the published sieve

Choose the fixed tuple size `K` large enough for M18 **684–703**, and a sufficiently small fixed `η>0` as allowed there. For example choose `K` to be a sufficiently large multiple of `400`. Given arbitrary target bands, choose

\[
 z=\eta\log X,\qquad C>\max(2,B/\eta).
\]

Use Lemma A and cover `[1,⌊Cz⌋]` by Lemma B, omitting

\[
 q=Z_{X^{4\eta}}
\]

if this is an exceptional prime. BFM **694–715, 770–784** gives `q≫log log X` whenever `q>1`, so eventually `q>v`. Thus its omission does not affect the fixed mesh primes or the smooth-difference property. The resulting modulus is exactly

\[
 W=\prod_{p\le\eta\log X,\ p\ne q}p,
 \qquad \log W=\eta\log X+o(\log X).
 \tag{6}
\]

The CRT residue `b` satisfies `gcd(∏(b+h_i),W)=1`. All shifts are below `X` eventually, and every prime factor of every difference is at most `v<η log X`. These are precisely the hypotheses at M18 **686–702** (also BFM **1035–1081**). The fixed-AP PNT used in the cover is not being substituted for this growing-modulus prime theorem.

M18 supplies a row `n∈[X,2X]`, `n≡b mod W`, containing primes in two of any four equal parts of the tuple. All nonprotected translates in the covered interval are composite: they have a covering prime at most `z` and exceed that prime. Ordering the prime tuple entries therefore gives **globally consecutive** primes among them. If the four parts occupy four ordered separated bands, choose two adjacent occupied parts and their last/first primes to get a cross-band globally consecutive pair.

There is no small bound on `B`: increasing `B` increases fixed `C,v` and the threshold for `X`, not the permitted `η`. This genuinely eliminates (1) for this existence application. It does not reproduce every quantitative/roughness clause of `DHL*`, nor force a prescribed pair of tuple entries to be prime. Incidentally, all protected translates in these rows are pairwise coprime, since every prime divisor of their differences divides `W`.

This gives another elementary covering route to the already known finite-point conclusions, not a new proof of Erdős #5. The older literature had already removed this kind of diameter limitation: see P14 **326–377, 594–634**, and M18 **778–827**. M18's last endpoint display at **825** omits the common translation `n`; actual endpoint heights are `n+h`, as used above.

## 3. Attempts to amplify the maximal initial interval

First, the unrestricted four-point theorem itself already recovers the qualitative initial interval: if missing bands accumulated at zero, choose just three `J_i,t_i` as in (3)–(4). Every positive difference of the four positions `0,t_3,t_2,t_1` would lie in their missing union (differences from zero are the `t_i` themselves). This contradicts M18 **32–37**. Thus eliminating the analytic diameter restriction yields an input already strong enough for the same qualitative conclusion, but not an identified interval endpoint.

Let

\[
 R=\sup\{r\ge0:[0,r]\subseteq L\}.
\]

P13 gives `R>0`. If finite, closedness gives `[0,R]⊆L`, and missing bands exist arbitrarily close to the right of `R`.

### 3.1 Moving Pintz's holes to the boundary fails algebraically

The decisive subtraction in (4) uses smaller holes converging to **zero**. If hole centers instead converge to `R>0`, subtracting two centers near `R` produces a number near zero, already in `L`, not another missing band near `R`. The inequalities `c_i>4δ_i>20c_(i+1)` cannot hold for centers all sufficiently close to positive `R`.

Translating all offsets changes no differences. Trying to add `R` to every pair difference is inconsistent already for three positions: writing their adjacent differences as `a,b`, one would need

\[
 R+(a+b)=(R+a)+(R+b),
\]

forcing `R=0`. Enlarging the allowed diameter does not repair this additive identity.

### 3.2 Rescaling the normalizer does not bootstrap

P14 allows much larger normalizers and still proves an ineffective initial interval: **87–112**, with the same lacunary-hole argument at **594–634**. Apply it to `f_A(j)=A log j`, for any fixed `A>0`. Exactly,

\[
 L_{f_A}=A^{-1}L,\qquad R_{f_A}=R/A.
\]

Thus its unknown `c_(f_A)` may shrink as `1/A`; the conclusion only gives `[0,A c_(f_A)]⊆L`. There is no uniform lower bound for `c_(f_A)` in the proof. Constant multiples also do not satisfy the diverging-quotient hypothesis of P14's “at most 98 exceptions” theorem (**101–113**).

Nor do known limit points concatenate automatically: even *simultaneously* realizing consecutive gaps near `x log p` and `y log p` gives a nonconsecutive endpoint difference near `(x+y)log p`. Covering a new interval does not remove the middle prime from that already realized configuration. No addition or dilation closure follows.

### 3.3 A precise counterexample to the proposed structural bootstrap

For any `R>0`, the closed set

\[
 S_R=[0,R]\cup[2R,\infty)
 \tag{7}
\]

has maximal initial interval exactly `[0,R]`, yet satisfies stronger finite-point conditions than the ones being used:

- Any three ordered real numbers have a pairwise difference in `S_R`: if both adjacent differences were in `(R,2R)`, their sum exceeds `2R`. Hence it satisfies M18's four-point conclusion (**32–37**).
- `μ(S_R∩[0,T])≥T/2`, stronger than the published `T/3` consequence, and it is syndetic.
- It also meets the normalized positional consequence of M18's multi-block proposition (**705–724**). Among any `M` real positions, some `⌈M/3⌉` have **all** pairwise distances in `S_R`: retain residues in a moving interval of length `R` modulo `3R`, and average. Retained points in the same period are at distance at most `R`; those in different periods are at distance at least `2R`. For `M=⌈3.99a⌉+1`, this supplies at least `a+1` positions.

This is not a model of the primes or a counterexample to Erdős #5. It proves a specific non-implication: **initial-interval knowledge plus these exact finite-point/block conclusions cannot force any extension of the maximal initial interval.** In particular, `[0,R]⊆L` does not exclude the small within-group differences that can satisfy an existential sieve conclusion. Also `3R/4∈S_R` but `3R/2∉S_R`, explicitly refuting addition/doubling closure as a consequence of just these structural properties.

## 4. Arithmetic repair attempted at that obstruction: optimize Pintz's statistic

I tried to turn the boundary obstruction into a contradiction using the actual block statistic, rather than positing a new positivity hypothesis. Its source is M18 **735–775** (the refinement of Pintz's argument), and its pair estimate is **353–390**.

For two candidate groups let `X_1(n),X_2(n)` count their prime entries. If a missing cross-band forces at most one group to be occupied, the pointwise statistic

\[
 X_1+X_2-\beta(\alpha)
   -\alpha\left(\binom{X_1}{2}+\binom{X_2}{2}\right)
 \le0,
 \quad
 \beta(\alpha)=\max_{\ell\ge1}\left(\ell-\alpha\binom\ell2\right)
 \tag{8}
\]

holds for every row. A positive weighted sum would contradict the missing band.

Allow unequal group sizes `λK,(1-λ)K`, and let `u` be the source's total first-moment parameter. With the source's symmetric test-function estimates, the certified scalar main-term lower bound is

\[
 F_K(u)=u-\beta(\alpha)
 -\frac{A\alpha}{2}\left(D-\frac1K\right)u^2,
 \qquad D=\lambda^2+(1-\lambda)^2\ge\tfrac12,
 \tag{9}
\]

apart from the source's small error terms. Here `A=3.99`, not a constant below `2`. The `1/K` term retains the exact unordered-pair count.

We can optimize this expression even allowing every `u>0`, a larger range than the source permits. Completing the square gives

\[
 \max_{u>0}F_K(u)
 =\frac1{2A\alpha(D-1/K)}-\beta(\alpha)
 \le\frac1{A\alpha(1-2/K)}-\beta(\alpha).
 \tag{10}
\]

The continuous maximum defining `β` is at `ℓ=1/α+1/2`. Rounding to its nearest positive integer loses at most `α/8`, so

\[
 \beta(\alpha)\ge\frac1{2\alpha}+\frac12.
\]

For `A=3.99` and `K≥5`, `A(1-2/K)>2`; hence (10) is strictly below `-1/2`. Therefore **neither tuning `α,u` nor unbalancing the groups produces a positive certified main term in this source family**. As `K→∞`, the threshold exposed by the calculation is `A<2`. M18 explicitly identifies that threshold at **188–189**.

This is a failure of the available lower-bound calculation, not an upper bound on the true weighted sum and not an impossibility theorem for all sieve weights. Shrinking the covering exponent `η` does not change the factor `A` in the published prime-pair estimate. The mesh's coprimality and smooth differences meet its hypotheses but supply no new pair-correlation estimate. Thus the attempted repair reaches the already identified occupancy issue with all arithmetic hypotheses now genuinely checked.

## 5. Verification and final status

The proofs of Lemmas A and B check the order of fixed parameters, exceptional-prime omission, smooth differences, reserve-prime capacity, and actual compositeness on the CRT row. Formula (5) checks the global prime-index normalization; any successful strict-band construction with an interior margin would give arbitrarily late indices.

As supplementary finite checks, exact-rational Python calculations passed 2,500 common-mesh placement cases (including overlapping bands), 15,979 asymmetric quadratic optimizations, 3,168 exact finite-`K` pair-count/optimization cases, 20,825 triples for the closed-set example, and its block-count inequality for `1≤a≤10,000`. These checks are not substitutes for the proofs above. No computational claim of prime existence was made.

`Submission/Spec.lean` was only hashed, not edited; its SHA-256 remained:

`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.

**Precise final failure:** the diameter/consecutivity loss in P13 can be eliminated for arbitrary prescribed finite-band geometry. What remains is not that elementary restriction: a single missing band above the maximal initial interval does not supply Pintz's lacunary family of missing pair differences. The published block statistic still cannot contradict concentration inside one allowed group. No valid addition/dilation closure, initial-interval amplification, or hit in every rational band `(a,b)` has been proved by this attempt.


## Independent follow-up verification

The main assistant independently read P13's intervening-prime subtraction and final lacunary-hole argument, M18's exact pair-bound and grouped-prime statements, and BFM's exceptional-prime bound. The common dyadic mesh has the stated fixed-parameter order, including when target bands overlap. Omitting a variable prime larger than `v` only adds one bounded-exponent factor to the smooth-survivor count, uniformly in that prime. Its eventual exclusion from the fixed smooth differences is justified by the cited lower bound on the exceptional prime. Thus both new compatibility lemmas meet the displayed growing-modulus sieve hypotheses.

The quadratic coefficient, the `1/K` correction, and the rounding bound for `β(α)` were also independently checked. The strictly negative optimized certificate is only a limitation of that certificate, not a negative theorem about the actual prime count. No inference from the initial interval to addition/dilation closure has been found. `Spec.lean` remains unmodified.