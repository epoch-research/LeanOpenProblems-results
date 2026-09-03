# All-scale prime-gap attempt: reciprocal cofactor holes and integer cancellation

## Outcome

**No proof or disproof of Erdős #5 was obtained.** The original two admitted declarations remain unchanged and were not used.

This attempt uses integer cofactor geometry, not factorial allocation, a gap-distribution model, or an assumed correlation estimate. Its proved arithmetic results are:

1. Every forced composite interval at a lower prime excludes an explicitly counted interval of **integer cofactor rows** at every sufficiently larger height. Exclusions from distinct lower prime gaps are disjoint and can be added.
2. Inside an upper interval of logarithmic length, fixed-row comparisons become subcritical once the cofactor exceeds a fixed constant. The bounded-cofactor exceptions are uniformly `o(H)` among its `H+O(1)` integer slots.
3. Allowing different cofactors gives an exact determinant inequality, localizing logarithmic prime-factor interactions to factors of size `O(sqrt(Y log Y))` or smaller.
4. An explicit Euclidean construction using **actual consecutive lower primes** realizes cancellation at that scale. It diagnoses why the repaired inference does not force a forbidden lower gap.

All these statements are proved below. The checker tests their finite identities, not the conjecture.

## 1. Hypothesis, global indices, and logarithmic height

Assume, for contradiction, that some `0<a<b` and some global index cutoff satisfy

\[
p_{n+1}-p_n\notin(a\log n,b\log n)\qquad(n\ge n_0).
\tag{H}
\]

Choose

\[
a<\alpha<A<B<\beta<b.
\]

For all sufficiently large primes `q`, (H) implies

\[
q^+-q\notin(\alpha\log q,\beta\log q),
\tag{1}
\]

where `q^+` is the next prime in the **global** sequence.

Here is an elementary justification of the change of normalization; PNT is not needed. For an integer `m>=1`,

\[
\frac{4^m}{2m+1}\le {2m\choose m}\le(2m)^{\pi(2m)}.
\]

The lower bound follows by taking the largest of the `2m+1` binomial coefficients. For the upper bound, the exponent of a prime `ell` in the central binomial coefficient is

\[
\sum_{j\ge1}\left(\left\lfloor\frac{2m}{\ell^j}\right\rfloor
 -2\left\lfloor\frac m{\ell^j}\right\rfloor\right).
\]

Each summand is 0 or 1, so `ell` raised to this exponent is at most `2m`. The exponent formula itself follows by counting multiples of each prime power in a factorial. Multiplying over primes proves the upper bound. Consequently `pi(x)>=c x/log x` for some absolute `c>0` and all sufficiently large `x` (take `2m<=x` with `x-2m<2`). Since the zero-based global index of a prime `q` is `pi(q)-1`,

\[
\log n=\log q+O(\log\log q),\qquad \frac{\log n}{\log q}\longrightarrow1.
\]

Also `n<=q`. Thus a gap in the interval in (1) would be in the forbidden interval in (H), after enlarging the height cutoff. This proves (1).

For the upper block in the question, take `X` sufficiently large and

\[
p\in(X,2X-B\log X],\qquad p^+-p>A\log X.
\]

If this gap were also `<B log X`, then

\[
\alpha\log p< A\log X<p^+-p<B\log X<\beta\log p,
\]

because `A log X>alpha log(2X)` eventually. This contradicts (1). Hence the gap is at least `B log X`, and every integer in

\[
(p+A\log X,p+B\log X)
\tag{2}
\]

is composite. The right endpoint is deliberately open.

At every lower prime `q` above the same fixed cutoff, `q^+-q>A log q` implies `q^+-q>=beta log q`. In particular

\[
J_q=(u_q,v_q):=(q+A\log q,q+B\log q)
\tag{3}
\]

contains only composite integers. The intervals `J_q` belonging to distinct such anchors are disjoint: each lies strictly between its anchor and its global successor.

## 2. First arithmetic implication: simultaneous reciprocal cofactor holes

**Lemma 1 (integer cofactor exclusion).** Let every integer in `(u,v)` be composite, where `1<u<v`. Fix an upper block

\[
I=[Y,Y+H],\quad H\ge0,\quad Y\ge2v.
\]

Define the set of integer rows

\[
\mathcal R(u,v;Y,H)
 =\mathbb Z\cap\left(\frac{Y+H}{v},\frac Yu\right).
\tag{4}
\]

For every `r` in this set and every integer `m` in `I`, if `r|m`, then `m/r` is composite. In particular no entry in row `r` can represent `m=r ell` with `ell` prime. Moreover

\[
|\mathcal R|\ge
\max\left\{0,\frac{Y(v-u)-Hu}{uv}-1\right\}.
\tag{5}
\]

**Proof.** Both inequalities defining (4) are strict. They give, for every `m` in `I`,

\[
u<Y/r\le m/r\le(Y+H)/r<v.
\]

Only when `r|m` do we use the composite-integer hypothesis. Also `r>(Y+H)/v>=2`, so these are proper cofactor rows. The length of the real interval in (4) is exactly

\[
L=\frac Yu-\frac{Y+H}{v}=\frac{Y(v-u)-Hu}{uv}.
\]

An open real interval of positive length `L` contains at least `L-1` integers; if it is empty the stated nonnegative lower bound still holds. This proves (5). ∎

For a lower forced interval (3), the exact length is

\[
L_q=
\frac{Y(B-A)\log q-H(q+A\log q)}
 {(q+A\log q)(q+B\log q)}.
\tag{6}
\]

This is a genuine all-scale consequence of (H), uniform in the position of the upper block, including an upper block (2). If `q` tends to infinity, the scale of (6) is

\[
L_q\asymp\frac{Y\log q}{q^2}
\]

whenever `Hq=o(Y log q)`. Thus lower holes well below `sqrt(Y log Y)` can exclude many integer rows, not just a single approximate quotient.

The simultaneous version also has no distributional input. For any finite collection of the disjoint intervals `J_q` with `2v_q<=Y`, their sets `R_q` in (4) are disjoint. Indeed, a row belonging to two of them would put `Y/r` in two disjoint intervals. Therefore

\[
\left|\bigcup_q\mathcal R_q\right|
 \ge\sum_q\max\{0,L_q-1\}.
\tag{7}
\]

### Exact failure of the first contradiction

The tempting next inference is that sufficiently many excluded rows leave too few prime-factor certificates for all the upper forced composites. **Row count is not certificate count.** Most rows do not divide a given upper integer; an occupied excluded row has a composite quotient, not a missing integer.

More precisely, if `m=r t` with composite `t` in a lower forced interval, choose a prime `ell|t`. Then

\[
m=\underbrace{r(t/\ell)}_{r'>r}\,\ell.
\tag{8}
\]

This is an exact integer refinement to a prime quotient in a different row. That quotient cannot lie in *any* of the forced composite intervals, since it is prime. Thus simultaneous exclusion of the rows in (7), by itself, never eliminates an actual prime-divisor representation. Factoring a composite quotient terminates at a prime, not at another forbidden interior point.

For example, the exact check with the actual consecutive primes `113,127`, the certified composite interval `(114,126)`, and `[Y,Y+H]=[100000,100100]` excludes 83 rows. Only 9 entries in those rows divide upper integers, and all 9 refine by (8). This is an identity/endpoints check, not a statistical model or an example of a missing normalized band.

## 3. Substantive repair: couple actual prime factors of different upper slots

To avoid counting inactive or non-prime-quotient rows, I next compared **actual prime factors** of different upper composites. The intended descent was to force two globally consecutive factor primes to have a gap in (1).

### Lemma 2: same-row dilution and a uniform exception bound

Fix `K>0`, `alpha>0`, a prime-factor threshold `Q>=3`, and an integer `R>max(1,K/alpha)`. Put `H=K log Y`. For sufficiently large `Y`, if `m=rq` belongs to `[Y,Y+H]`, `q>=Q`, and `r>=R`, then

\[
H/r<\alpha\log q.
\tag{9}
\]

Consequently any two prime quotients `q<q'` occurring in the **same** such row differ by less than `alpha log q`.

**Proof.** Set `y=Y+H`. Since `q<=y/R` and `log t/t` decreases for `t>=3`,

\[
r\log q\ge Y\frac{\log q}{q}
 \ge\frac{YR}{y}\log(y/R)=(R+o(1))\log Y.
\]

The error is independent of the row and prime factor. Since `alpha R>K`, this proves (9). The quotient interval in a fixed row has length `H/r`. ∎

The exceptions with `r<R` are sparse in every block, not merely on average. Let

\[
E_R(I)=\{m\in I\cap\mathbb N:m=rq,
       \ 1\le r<R,\ q\text{ prime}\}.
\]

Then, for fixed `R` and `H` tending to infinity with `Y`,

\[
|E_R(I)|=o(H).
\tag{10}
\]

**Proof.** Fix a finite prime bound `z`, let `M` be the product of primes at most `z`, and let `phi(M)` count the coprime residue classes. Eventually all relevant prime quotients exceed `z`. Counting these residue classes in each interval `[Y/r,(Y+H)/r]` gives

\[
|E_R(I)|\le H\frac{\varphi(M)}M\sum_{r<R}\frac1r
                   +(R-1)\varphi(M).
\tag{11}
\]

First let `Y,H` tend to infinity with `R,M` fixed. Then let `z` tend to infinity. By finite inclusion–exclusion, `phi(M)/M` is the product of `1-1/ell` over the primes dividing `M`. This ratio tends to zero: the product of the convergent geometric series for the finitely many primes at most `z` contains every term `1/n` for `n<=z`, so

\[
\frac M{\varphi(M)}
 =\prod_{\ell\le z}(1-1/\ell)^{-1}
 \ge\sum_{n\le z}\frac1n\longrightarrow\infty.
\]

This proves (10), uniformly in block location. ∎

There are also only boundedly many slots having no prime factor at least the fixed `Q`. To see this, let `S` be the finite set of primes below `Q`, of size `s`. An `S`-smooth integer `m>=Y` has some prime-power component at least `Y^(1/s)`. For each `ell` in `S`, let `ell^e` be its least power at least this threshold. Once `H<Y^(1/s)`, each of these `s` powers divides at most one integer in the block. Hence there are at most `s` such smooth slots.

Thus, outside `o(H)+O_Q(1)` slots, there are actual prime factors above `Q`, and every prime factor's cofactor is at least `R`. Same-row prime pairs there are subcritical by (9).

**Scope warning.** This does *not* say a short quotient interval cannot lie inside a forced lower hole anchored outside it. Lemma 1 describes exactly that possibility. Nor is (10) a relative estimate for prime-centered or rough-number masks: its denominator is all integer slots, and `R` is fixed.

### Lemma 3: different rows force a square-root-scale interaction

Let

\[
m=rq,\qquad m'=sq',\qquad m,m'\in[Y,Y+H],\quad q<q'.
\]

All four factors are positive integers; primality is not needed for this lemma. If `r!=s`, then

\[
q(q-H)\le(Y+H)(q'-q).
\tag{12}
\]

**Proof.** With `delta=q'-q`,

\[
q(r-s)=m-m'+s\delta.
\]

Since `|r-s|>=1` and `s<= (Y+H)/q'<= (Y+H)/q`,

\[
q\le H+s\delta\le H+\frac{Y+H}{q}\delta.
\]

Multiplication by `q` proves (12). ∎

In particular, if `q'-q<=D log q`, then

\[
q\le T_Y:=
\frac{H+\sqrt{H^2+4(Y+H)D\log(Y+H)}}2
 =O_{K,D}(\sqrt{Y\log Y}).
\tag{13}
\]

After removing (10), any pair of actual factor primes with `q>=Q` and

\[
\alpha\log q\le q'-q\le D\log q
\]

must be in different rows by (9), and hence satisfy (13). The larger factor `q'` obeys the same order bound. This confines the possible descent; it does **not** prove such a pair exists or that an extracted pair is globally consecutive.

## 4. Exact obstruction to the repair: Euclidean near-collisions

One might still hope that two close products in the remaining range force a forbidden factor gap. The following exact construction shows why short product separation does not give that inference.

**Lemma 4.** Let `q<q'=q+delta` be actual consecutive primes, with

\[
4\le\delta<q/2.
\]

Let `s` be the largest odd integer at most `2q/delta`, and set

\[
r=s+2,\quad x=qr,\quad y=q's,\quad d=2q-s\delta.
\]

Then

\[
3\le s<r<q,\qquad 0<d<2\delta,\qquad x-y=d.
\tag{14}
\]

Both `x,y` are odd composite integers. Their largest prime factors are respectively `q,q'`, so the factor primes really are globally consecutive.

**Proof.** The choice of the largest odd integer gives

\[
2q/\delta-2<s\le2q/\delta.
\]

This proves `0<=d<2 delta`. Equality `d=0` would say the even number `delta>=4`, which is smaller than `q`, divides `2q`; this is impossible for the odd prime `q`. The assumption `2q/delta>4` gives `s>=3`, while `delta>=4` gives `r<=q/2+2<q`. Both cofactors are odd. Finally

\[
q(s+2)-(q+\delta)s=2q-s\delta=d.
\]

The cofactors are greater than 1 and less than `q`, proving the assertions about compositeness and largest prime factors. ∎

The height satisfies the exact estimates

\[
\frac{2q^2}{\delta}<x\le\frac{2q^2}{\delta}+2q,
\qquad
\frac{2q^2}{\delta}-2\delta<y\le\frac{2q^2}{\delta}+2q.
\tag{15}
\]

If along a sequence with `q -> infinity` the supplied lower gaps satisfy `delta/log q -> lambda` with `0<lambda<infinity`, (15) gives, with `Y=y`,

\[
\log Y\sim2\log q,\qquad
\frac{q^2}{Y\log Y}\longrightarrow\frac\lambda4,
\qquad 0<x-y<2\delta=(\lambda+o(1))\log Y.
\tag{16}
\]

This is only an algebraic implication **if those inputs are supplied**; it asserts no existence of gaps at a specified `lambda`. It shows that the square-root scale in (13) is a real cancellation scale, not an error term that may simply be discarded.

For the explicit consecutive primes `23,29`, the construction gives

\[
207=9\cdot23,\qquad203=7\cdot29,\qquad207-203=4.
\]

The failed inference is now precise: from `|rq-sq'|=O(log Y)`, one cannot drop the term `q(r-s)` and infer a comparably small or forbidden `q'-q`. At the scale in (16), `q(r-s)` and `s(q'-q)` cancel. Assuming `r=s` would evade that cancellation, but (9) then puts the factor gap below the forbidden band. The construction works with whatever consecutive lower gap is actually supplied; under (H), such a gap is simply on an allowed side of (1).

This is not a countermodel to the conjecture. In particular, the upper endpoints in (14) are **provably composite**, and the remainder `d` has not been placed in any prescribed normalized band.

## 5. What remains unproved

Neither the counted cofactor holes nor the repaired determinant comparison forces a contradiction to (H). No relative correlation bound has been postulated as though proved.

The missing step would have to use additional arithmetic beyond the implications above to force an actual forbidden **globally consecutive prime pair**. The present construction fails the required endpoint audit:

- **Upper endpoint primality:** fails; the constructed `x,y` are proper products.
- **Upper global consecutivity:** not established; global consecutivity is retained only for their lower largest prime factors.
- **Height/global index:** (4) is uniform at upper height, but (14) gives no prime endpoints there, hence no qualifying global index `n>=N0`.
- **Arbitrary band:** neither the Euclidean remainder `d` nor an upper prime gap has been placed in `(a log n,b log n)`.

Thus this report supplies new proved arithmetic implications and an exact failure/repair diagnosis, not a solution of either declaration in `Spec.lean`.

## 6. Sources and verification

No analytic prime-distribution theorem, conjecture, or admitted declaration is imported into the argument. The normalization bound is proved in §1; the local sieve bound is proved in §3.

Project/source lines used to identify the target and elementary background:

- `Submission/Spec.lean:37–40`: the definition of `normalizedGap`; `:55–66`: the statement being attempted, **not** its admitted proof. `:73` is likewise unused.
- `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean:24–27`: `primeGap n` is the difference of the globally adjacent `Nat.nth Nat.Prime` values.
- `.lake/packages/mathlib/Mathlib/NumberTheory/PrimeCounting.lean:45–56,74–80,100–102`: counting conventions, the zero-based global index, and primality of the enumerated terms.
- `.lake/packages/mathlib/Mathlib/Data/Nat/Prime/Defs.lean:402–403`: existence of a prime divisor; `.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Defs.lean:97–100`: reconstruction from prime powers. Only these elementary factorization facts, not any gap theorem, are used as mathematical background.

Verification command:

```text
python3 Submission/check_all_scale_prime_gap.py
```

The checker uses exact integers and rational numbers. It verified 120 binomial/index instances, 36 reciprocal-row cases (including 113 occupied-entry refinements), 36 sieve/smooth-bound instances, 77,579 determinant instances, and 540 instances of the Euclidean identity on consecutive-prime inputs. It does not search for a counterexample to the normalized-gap assertion. The written proofs, not these finite tests, justify the general lemmas.

`Spec.lean` SHA-256 before and after this attempt:

```text
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```
