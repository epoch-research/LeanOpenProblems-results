# Height-controlled construction: protected smooth shifts and simultaneous sieving

## Outcome and scope

**The requested theorem is not proved.** This attempt does prove a height-controlled arithmetic near-miss, including simultaneous endpoint survival, rather than assuming a prime-pair lower bound:

> **Proved construction.** Fix real numbers `0 < A < B` and `0 < η < 3/40`. For every sufficiently large real `X`, there are an integer
> 
> \[
> A\log X<h<B\log X,
> \]
> 
> a squarefree modulus `W = X^{η+o(1)}`, and a residue `r (mod W)` such that:
> 
> 1. Every `n ∈ [X,2X]` with `n ≡ r (mod W)` has **every integer strictly between `n+h` and `n+2h` composite**.
> 2. The two endpoints are coprime to each other and to `W`.
> 3. There are
> 
> \[
> \gg \frac XW\left(\frac{\log\log X}{\log X}\right)^2
> \]
> 
> such translates for which **both endpoints have no prime factor at most `X^{1/10}`**. Each endpoint consequently has at most ten prime factors, counted with multiplicity.

Thus both endpoint conditions are obtained simultaneously at the prescribed exponential height, but they are roughness/almost-primality conditions, not primality. The endpoints are consecutive among the `X^{1/10}`-rough integers in their interval. They are **not asserted to be consecutive primes**, nor consecutive ten-almost-primes.

The proof below uses ordinary PNT, PNT in a **fixed** arithmetic progression, and Mertens' theorem. The progression in the PNT input depends on `A,B,η` but does not grow with `X`. No prime-pair theorem, uniform growing-modulus prime theorem, or premise from `Spec.lean` is used. The simultaneous sieve estimate is proved below by explicit finite polynomials.

Two repairs are then calculated: least-prime-factor switching, with re-sieving of its branches, and extension to the enclosing global prime gap. Neither closes the target.

## 1. Exact height and index normalization

For the original interval `(a,b)`, choose `a < A < B < b`. If the construction could produce two prime endpoints, they would be globally consecutive, at heights in `[X,3X]`, and their gap would be `h`.

For a prime `p ∈ [X,3X]` with index `j=π(p)`, PNT gives, uniformly in that range,

\[
\frac{\log j}{\log X}\longrightarrow 1.
\]

Hence `A log X < h < B log X` would imply `a log j < h < b log j` for all sufficiently large `X`. Also `j ≥ N₀` eventually. This normalization is not a remaining obstacle.

## 2. A protected covering lemma

Write `P(y)=∏_{p≤y}p`.

### Lemma 1: an elementary cover protecting prescribed smooth points

Fix `C≥2` and an integer `k≥1`. There is a fixed `v≥max(3,2C,k)` with the following property. For every sufficiently large `z`, let `H_z` be any set of at most `k` integers in `[1,⌊Cz⌋]`, each divisible by `Q=P(v)` and having all its prime factors at most `v`. One can choose one residue `a_p (mod p)` for every prime `p≤z` such that:

* no member of `H_z` belongs to any of the chosen residue classes;
* every other integer in `[1,⌊Cz⌋]` belongs to at least one chosen class.

In particular, CRT gives a residue `r (mod P(z))` for which every translate `n≡r` makes all the unprotected positions composite, provided `n>z`.

### Proof

For `p≤v`, initially choose `a_p=1`. For `v<p≤z/2`, choose `a_p=0`. Reserve the primes in `(z/2,z]`.

Let `S` be the integers in `[1,Cz]` surviving these initial choices. A survivor either is `v`-smooth or has the form

\[
 t=m\ell,\qquad 1\le m\le\lfloor2C\rfloor,\quad \ell>z/2\text{ prime}.
\]

Indeed, every prime factor in `(v,z/2]` was removed. If there is a factor greater than `z/2`, there cannot be two such factors when `z>4C`; its cofactor is less than `2C`.

For a fixed positive integer `m`, put

\[
 \sigma_v(m)=
 \prod_{\substack{p\le v\\p\nmid m}}\frac{p-2}{p-1}.
\]

This is the proportion of reduced residue classes `c (mod Q)` for which `mc≠1 (mod p)` for all `p≤v`. A factor at `p=2` makes this zero when `m` is odd. For every fixed `m`, `σ_v(m)→0` as `v→∞`: excluding the finitely many primes dividing `m` does not affect divergence of the sum of reciprocal primes.

Choose `v` so large that

\[
 C\sum_{m\le\lfloor2C\rfloor}\frac{\sigma_v(m)}m<\frac1{16}.
\]

Now `v` and `Q` are fixed. PNT in the finitely many relevant residue classes modulo `Q` bounds the number of surviving primes `ℓ≤Cz/m` by

\[
 \left(\frac C m\sigma_v(m)+o(1)\right)\frac z{\log z}.
\]

Ignoring the lower restriction `ℓ>z/2` only increases this bound. The number of `v`-smooth integers at most `Cz` is

\[
 O_v((1+\log z)^{\pi(v)})=o(z/\log z),
\]

by counting possible exponents of the finitely many primes at most `v`. Consequently

\[
 |S|\le\frac z{8\log z}
\]

for all sufficiently large `z`.

Every protected point survives: it is `0`, not `1`, modulo each prime at most `v`, and no larger prime divides it. The reserve contains

\[
 \pi(z)-\pi(z/2)\sim\frac z{2\log z}
\]

primes. Assign a different reserve prime to each `t∈S\setminus H_z`. When assigning a prime to `t`, exclude primes dividing any nonzero difference `t-h_i`, `h_i∈H_z`. Each difference has absolute value at most `Cz` and has at most one prime divisor greater than `z/2` when `z>4C`. Thus at most `k` reserve primes are forbidden for this reason. The reserve is much larger than `|S|+k`, so the greedy assignment succeeds.

For the assigned prime `p`, set `a_p=t (mod p)`. For each unused reserve prime choose any residue avoiding the protected points; this is possible because `p>k`. This covers all unprotected points and none of the protected points.

Finally take `r≡-a_p (mod p)` for all `p≤z`. A covered translate `n+t` is divisible by its covering prime and exceeds that prime when `n>z`, so it is composite. Protected translates are coprime to `P(z)`. This proves the lemma. ∎

### Lemma 2: putting protected points into a logarithmic band

For fixed `Q>0` and `0<c₁<c₂`, every sufficiently large `z` admits

\[
 Q2^u3^w\in(c_1z,c_2z),\qquad u,w\in\mathbb Z_{\ge0}.
\]

**Proof.** The ratio `log 3/log 2` is irrational, since no positive power of `2` is a positive power of `3`. The nonnegative multiples of `log 3` are therefore dense modulo `log 2`. For any fixed `δ>0`, a finite initial segment is a `δ/3`-net of that circle. Applying this net at the point `t+δ/2` modulo `log 2`, for all sufficiently large `t`, some one of those finitely many `w` and a nonnegative integer `u` therefore satisfy

\[
 t<u\log2+w\log3<t+\delta.
\]

Choose `δ<log(c₂/c₁)` and `t=log(c₁z/Q)`. Exponentiating proves the assertion. The elementary density statement follows, for example, by the pigeonhole proof of density of an irrational rotation; it is not a prime-distribution assertion. ∎

### Application of the cover

Set `z=η log X` and choose a fixed `C>max(2,2B/η)`. Obtain `v,Q` from Lemma 1 with `k=2`. Lemma 2 supplies a `v`-smooth multiple `h=Q2^u3^w` in `(A log X,B log X)` for every sufficiently large `X`.

Protect exactly `h,2h`, both lying in `[1,Cz]`. Let `W=P(z)` and let `r` be the resulting CRT residue. PNT gives

\[
 \log W\sim z,\qquad W=X^{\eta+o(1)}.
\]

The integers `n∈[X,2X]`, `n≡r (mod W)`, can be written `n=r+Wj` with `j` in an interval of

\[
 Y=X/W+O(1)=X^{1-\eta+o(1)}
\]

consecutive integers. All integers between `n+h` and `n+2h` are composite. Also

\[
 \gcd(n+h,n+2h)=1:
\]

any common prime factor would divide `h`, whose prime factors all divide `W`, whereas both endpoints are coprime to `W`.

This already settles the cover and height issues. The next step actually counts simultaneous endpoint survivors.

## 3. An explicit simultaneous lower sieve

The following auxiliary lemma is stated slightly generally because it will also be applied to the switching branches.

### Lemma 3: a two-form sieve with a proved positive main term

Let `j` range over `Y` consecutive integers. Consider two integer linear forms `F₁(j),F₂(j)` such that for every prime `p∈(z,T]` their product vanishes at exactly two distinct residues modulo `p`. Consequently, CRT gives exactly `2^{ω(d)}` roots modulo every squarefree product `d` of these primes.

Let `S(z,T)` count the `j` for which neither form is divisible by a prime in `(z,T]`, and put

\[
 V(z,T)=\prod_{z<p\le T}(1-2/p),\qquad D=T^{37/4}.
\]

For sufficiently large `z`, uniformly in `T>z` and the forms,

\[
 \frac1{20}YV(z,T)-D(1+\log D)
 \le S(z,T)
 \le 3YV(z,T)+D(1+\log D).                 \tag{3.1}
\]

### Proof

If there are no primes in `(z,T]`, the bounds are immediate. Otherwise partition `(z,T]` into blocks

\[
 \mathcal P_i=\{p:\max(z,T^{2^{-(i+1)}})<p\le T^{2^{-i}}\},
\]

ending with the last nonempty block. Every block lies in an interval `(u,u²]` with `u≥z`. Put `g_p=2/p`. Uniformly over the blocks, Mertens' theorem gives, for sufficiently large `z`,

\[
 \mu_i:=\sum_{p\in\mathcal P_i}g_p\le\frac75,
 \qquad
 V_i:=\prod_{p\in\mathcal P_i}(1-g_p)\ge\frac6{25}.       \tag{3.2}
\]

For the second bound use `log V_i=-μ_i+O(1/z)` and the strict elementary inequalities

\[
 2\log2<\frac75<\log(25/6).
\]

Take odd truncation orders

\[
 r_i=\max(5,2i-3).
\]

Thus the first five orders are `5`, and the later orders are `7,9,11,…`. If `M_i(j)` is the number of primes in block `i` dividing `F₁(j)F₂(j)`, define

\[
 U_i(j)=\sum_{s=0}^{r_i-1}(-1)^s{M_i(j)\choose s},
 \qquad E_i(j)={M_i(j)\choose r_i},
 \qquad I_i(j)=\mathbf1_{M_i(j)=0}.
\]

The finite binomial identities give

\[
 0\le I_i\le U_i,\qquad U_i-E_i\le I_i.
\]

For example, when `M_i≥1`, the even partial sum `U_i` is `binom(M_i-1,r_i-1)`, while the odd partial sum `U_i-E_i` is `-binom(M_i-1,r_i)`.

Since all the `U_i` are nonnegative, telescoping the difference of two products gives the pointwise lower bound

\[
 \prod_i I_i \ge
 \mathcal L:=\prod_iU_i-\sum_iE_i\prod_{\ell\ne i}U_\ell.       \tag{3.3}
\]

Also `∏ I_i≤∏ U_i`.

To evaluate the main terms of these finite polynomials, introduce independent Bernoulli variables with parameters `g_p`. **This is just an algebraic device to evaluate a finite polynomial, not a probabilistic assumption about primes.** Write `u_i` for the expectation of `U_i`, and `δ_i` for that of `E_i`. Then

\[
 V_i\le u_i\le V_i+\delta_i,
 \qquad
 \delta_i\le\frac{\mu_i^{r_i}}{r_i!}.
\]

The factorial bound is the elementary inequality between an elementary symmetric sum and the corresponding power sum. Consecutive odd factorial terms starting at order `7` have ratio at most

\[
 \frac{(7/5)^2}{8\cdot9}<\frac1{36}.
\]

Therefore

\[
 \sum_i\frac{\delta_i}{V_i}
 \le\frac{25}{6}\left(5\frac{(7/5)^5}{5!}
              +\frac{36}{35}\frac{(7/5)^7}{7!}\right)
 =\frac{10605217}{11250000}<\frac{19}{20}.                \tag{3.4}
\]

Independence between blocks now gives

\[
 \mathbb E\mathcal L
 =\prod_i u_i\left(1-\sum_i\frac{\delta_i}{u_i}\right)
 \ge\frac1{20}\prod_iV_i=\frac1{20}V(z,T),
\]

and

\[
 \mathbb E\prod_iU_i
 \le V(z,T)\exp\left(\sum_i\delta_i/V_i\right)<3V(z,T).
\]

It remains to justify using these as main terms for the actual integer sequence, with a sufficiently small error. Expand (3.3) as a divisor sum

\[
 \mathcal L(j)=\sum_d c_d\,\mathbf1_{d\mid F_1(j)F_2(j)}.
\]

All occurring `d` are squarefree. Also `|c_d|≤1`. Indeed, a term from `∏U_i` uses at most `r_i-1` primes in every block. A term from `E_i∏_{ℓ≠i}U_ℓ` uses exactly `r_i` in block `i` and at most `r_ℓ-1` in all other blocks. These supports are mutually disjoint.

The divisor sizes are controlled because

\[
 \sum_{i\ge0}(r_i-1)2^{-i}=\frac{33}{4}.
\]

A term with one `E_i` adds at most `2^{-i}≤1` to this exponent. Hence every occurring divisor is at most `T^{37/4}=D`.

For each such `d`, exact residue counting gives

\[
 \#\{j:d\mid F_1(j)F_2(j)\}
 =Y\frac{2^{\omega(d)}}d+O(2^{\omega(d)}),
\]

with absolute error at most `2^{ω(d)}`. Thus the total absolute error is at most

\[
 \sum_{d\le D}2^{\omega(d)}
 \le\sum_{d\le D}\tau(d)
 \le D(1+\log D).
\]

The same reasoning applies to the upper polynomial `∏U_i`. Their main terms are exactly the polynomial expectations already evaluated. This proves (3.1). ∎

### Apply the sieve to the protected endpoints

For `n=r+Wj`, use

\[
 F_1(j)=r+Wj+h,\qquad F_2(j)=r+Wj+2h.
\]

Every prime `p>z` is coprime to `W` and does not divide `h`, since `h` is `v`-smooth. Thus the two forbidden residues are distinct, and Lemma 3 applies with

\[
 T=X^{1/10},\qquad D=X^{37/40}.
\]

Because `η<3/40`,

\[
 D(1+\log D)=o\big(YV(z,T)\big).
\]

Here Mertens' theorem gives

\[
 V(z,T)=(1+o(1))\left(\frac{\log z}{\log T}\right)^2
       =(100+o(1))\left(\frac{\log z}{\log X}\right)^2.       \tag{3.5}
\]

The first equality follows by comparing `(1-2/p)` with `(1-1/p)^2`; the logarithm of their ratio, summed over `p>z`, is `O(1/z)`.

Let `S(T)` denote the number of resulting simultaneous rough pairs. We have proved the useful two-sided bounds

\[
 (5-o(1))Y\left(\frac{\log z}{\log X}\right)^2
 \le S(T)
 \le(300+o(1))Y\left(\frac{\log z}{\log X}\right)^2.       \tag{3.6}
\]

The endpoints were already coprime to every prime at most `z`, so they are now free of prime factors at most `T`. They lie in `[X,3X]`. If either had eleven prime factors counted with multiplicity, it would exceed

\[
 T^{11}=X^{11/10}>3X
\]

for sufficiently large `X`. Each therefore has at most ten prime factors. This finishes the proved construction stated at the beginning.

## 4. First repair: reach primality by sieving or least-factor switching

### 4.1 Direct prime-certifying sieve: the error becomes unusable

To certify that both endpoints are prime, one could try the same argument at

\[
 T_*=(3X)^{1/2}.
\]

An integer in `[X,3X]` with no prime factor at most `T_*` is prime. But the actual polynomial just proved then has level

\[
 D_*=T_*^{37/4}=(3X)^{37/8},
\]

and the coefficientwise CRT error bound is vastly larger than its main term. Thus (3.1) supplies no positivity at the prime-certifying cutoff. Discarding high-divisor terms is not a valid repair: it discards part of the pointwise Bonferroni lower polynomial.

This is a failure of this particular bound, not a proof that every conceivable sieve must fail.

### 4.2 An exact switching identity

Keep `T=X^{1/10}` and write the endpoints as `u=n+h`, `v=n+2h`. Let `C_pp(X)` count translates having both endpoints prime. For `i=1,2` and primes

\[
 T<q\le(3X)^{1/2},
\]

let `B_i(q)` count translates satisfying:

* `q` divides endpoint `i`;
* neither endpoint has a prime factor smaller than `q`.

Since `gcd(u,v)=1`, the least prime factor of `uv` divides exactly one endpoint. Every pair counted by `S(T)` that is not a prime pair has such a least factor at most `(3X)^{1/2}`. Conversely every term `B_i(q)` is one of those non-prime pairs. These cases are disjoint. Therefore

\[
 C_{pp}(X)=S(T)-\sum_{i=1}^2\sum_{T<q\le\sqrt{3X}}B_i(q).       \tag{4.1}
\]

This is an exact arithmetic decomposition, not a conjectural estimate.

For a fixed `q`, the divisibility condition puts `j` in one residue modulo `q`. Writing `j=j_i+qs`, the endpoints become

\[
 q(Ws+c),\qquad q(Ws+c)\pm h,                         \tag{4.2}
\]

over an interval of `Y/q+O(1)` values of `s`. The sign depends on which endpoint is divided. This identifies the specific arithmetic branches that must be controlled.

### 4.3 The first bound fails; retaining roughness still does not close it

Dropping the least-factor restriction yields

\[
 B_i(q)\le Y/q+O(1).
\]

By Mertens,

\[
 \sum_{i,q}B_i(q)\le(2\log5+o(1))Y,
\]

since `log(sqrt(3X))/log T→5`; the sum of the `O(1)` errors is `o(Y)`. But (3.6) gives `S(T)=o(Y)`. Thus this first actual subtraction is useless.

A better repair is to preserve roughness in each switched branch instead of discarding it. Set

\[
 N_q=Y/q+O(1),\qquad T_q=N_q^{1/10}.
\]

Here `N_q` is the length in the particular branch under consideration (the two lengths can differ by one). Uniformly over this range of `q`, `N_q≥X^{1/2-η+o(1)}` and `z<T_q<T<q`. The two forms (4.2) still have exactly two distinct roots modulo every prime in `(z,T_q]`: those primes divide neither `Wq` nor `h`. Each `B_i(q)` satisfies these roughness conditions, so the **upper** half of Lemma 3 applies. Its error is `N_q^{37/40}(1+O(log N_q))`, negligible compared with its main term uniformly in `q`. Consequently

\[
 B_i(q)\le(300+o(1))\frac Yq
                 \frac{(\log z)^2}{(\log(Y/q))^2}.       \tag{4.3}
\]

This is a genuine order-of-magnitude improvement over the unsieved branch bound.

Put

\[
 I_\eta=\int_{1/10}^{1/2}\frac{dt}{t(1-\eta-t)^2}.
\]

PNT and partial summation, using `log Y/log X→1-η`, give from (4.3)

\[
 \sum_{i,q}B_i(q)
 \le(600I_\eta+o(1))Y
          \left(\frac{\log z}{\log X}\right)^2.          \tag{4.4}
\]

The sum of the branch errors is negligible as well; alternatively this follows directly from the preceding uniform relative-error statement. Notice that

\[
 I_\eta>\int_{1/10}^{1/2}\frac{dt}{t}=\log5>1.
\]

Combining the proved bounds (3.6) and (4.4) in (4.1) gives only

\[
 C_{pp}(X)\ge
 \big(5-600I_\eta-o(1)\big)Y
       \left(\frac{\log z}{\log X}\right)^2,
\]

whose coefficient is negative. Even after retaining roughness and re-sieving every branch, this repair does not leave a positive prime-pair count.

For `q>(3X)^{1/3}`, the cofactor `Ws+c` in (4.2) is itself prime. It exceeds one because the endpoint is at least `X>q`; if it were composite, its factors, all at least `q`, would make the original endpoint at least `q³>3X`. Thus the late branches already include a genuinely bilinear prime/cofactor problem. The exact local residue counts used in Lemma 3 do not give the cancellation needed between these branches and `S(T)`.

**Precise unresolved implication on this route:** establish positivity of the signed expression (4.1), for these constructed shifts and residues at these heights. No such positivity is assumed. The calculated lower and upper bounds have the wrong constants to establish it; improving merely the coverage, endpoint height, or number of CRT translates does not repair that calculation.

## 5. Distinct repair: extend the rough corridor to actual neighboring primes

One might avoid simultaneous endpoint primality by replacing the rough endpoints with their enclosing primes. This does produce a global consecutive-prime gap, but not its upper logarithmic bound.

For any constructed corridor `[u,u+h]`, let `P` be the largest prime at most `u`, and let `Q` be the next prime. There is no prime strictly between the corridor endpoints, hence

\[
 P\le u<u+h\le Q.
\]

These `P,Q` are globally consecutive. Bertrand's theorem gives `P≥X/2` and `Q≤6X` for sufficiently large `X`, so their height is still comparable to `X`, and

\[
 Q-P\ge h>A\log X.
\]

The missing inequality is `Q-P<B log X`.

Here is a counting test of this repair. A global prime gap of length `g≥h` can contain at most

\[
 1+\left\lfloor\frac{g-h}{W}\right\rfloor                 \tag{5.1}
\]

of our corridors, because their left endpoints all belong to the same residue class modulo `W` and must lie in an interval of length `g-h`.

If every enclosing gap failed the desired upper bound, each would have length at least `B log X`. Distinct such gaps are disjoint and lie in `[X/2,6X]`. Their number is `O(X/(B log X))`, and the sum of their lengths is `O(X)`. Therefore (5.1) only gives

\[
 S(T)\le O\left(\frac X{B\log X}+\frac XW\right).         \tag{5.2}
\]

This is fully compatible with (3.6), which is smaller even than `X/W` by a factor tending to zero. Thus the many simultaneously rough corridors cannot, on these estimates, force one enclosing gap into the requested upper band. Counting them without the multiplicity bound (5.1) would be invalid.

This is a different failure from applying Dirichlet or Linnik separately to endpoint classes: it is the loss of control on the two endpoint extensions, with the multiplicity obstruction made explicit.

## 6. Conclusion and integrity

The construction has genuine closure through the following arithmetic lemma: **every fixed positive logarithmic band contains the length of a prime-free corridor at every sufficiently large height, with many simultaneous, coprime, ten-almost-prime endpoint pairs.** The protected cover has a proof, its modulus has the required exponential-size relation to the height, and the simultaneous endpoint lower bound has a proof.

The actual Erdős #5 target remains open in this attempt. We have not shown that both endpoints can be made prime, nor that extension to enclosing primes preserves the upper band. The two attempted repairs above specify and calculate those failures, rather than using either assertion as a premise.

No Lean proof of the original target was attempted because there is no mathematical closure of that target. No axiom, `sorry`-backed helper, or premise from `Submission/Spec.lean` was introduced. `Submission/Spec.lean` was not edited; its checked SHA-256 is

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

and it retains its two original `sorry` occurrences.

## Independent follow-up check

The main assistant independently checked the proof, including §§3–5. For the sieve, the block Mertens estimates are uniform because each block is contained in `(u,u²]` with `u≥z`; the nonnegative upper polynomials and the telescoping product inequality give the stated lower polynomial. Its divisor supports are disjoint, so `|c_d|≤1`, and the exact support exponent is `33/4+1=37/4`. Exact rational arithmetic confirmed (3.4), and finite independent checks confirmed the binomial identities and 20,736 four-block product inequalities. These tests supplement, rather than replace, the displayed general proof.

The switched branch estimate uses `N_q≥X^(1/2−η+o(1))`, making its error uniformly negligible. Partial summation gives the stated integral `I_η`; the coefficient `5−600 I_η` is strictly negative. The least-factor decomposition is exact because both endpoints exceed every possible least factor in its range and their gcd is one. The enclosing-gap multiplicity bound is also valid but too weak. Thus the checked construction still does not supply two prime endpoints or a prime gap below `B log X`.


## Additional checked lead: retiming a Maier matrix

A subsequent independent strategy pass checked Ford–Maynard–Tao, *Chains of large gaps between primes*, `/corpus/src/1511.04468/1511.04468.tex`, lines 194–287. The source constructs, at a sieve parameter `x`, a row of width

\[
y=cx\log x\,\log_3 x/\log_2 x
\]

with `|T|≍Kx/log x` surviving columns, for each fixed `K`. The modulus is the primorial through `x`, possibly with one exceptional prime removed; `log P∼x` and `P/φ(P)≍log x`. At its native height `exp(O(x))`, first and second moments give rows with `≍K` primes. Deleting close-pair events yields a minimum gap `εy` with `ε` a sufficiently small multiple of `K⁻²`. This is a large-gap-chain result, not a finite normalized-band result.

If instead the same rows are placed at heights with `log X≍y`, Brun–Titchmarsh gives the following genuine upper bound. For uniformly chosen `n∈[X,2X]` in the row residue modulo `P`, each retained column has prime probability

\[
\ll \frac{P}{\varphi(P)\log(X/P)}.
\]

Indeed its prime count is at most the count in its reduced class up to `3X`, and the number of available translates is `X/P+O(1)`. Summing over the columns therefore gives

\[
\mathbb E\#\{t\in T:n+t\text{ prime}\}
\ll\frac{Kx}{\log X}\asymp\frac{Kx}{y}=o(1)
\]

for fixed `K`. The main assistant independently checked the cited source passages and this calculation. It removes the large-first-moment input used in the source after retiming; it does not exclude rare successful rows. At the native height there is still no upper logarithmic bound on a selected gap. No closure of either unresolved endpoint condition was found through this lead.