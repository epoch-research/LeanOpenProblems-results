# Erdős 371: uniform growing-dilation stability — new consequences and countermodel tests

## Status (including what is **not** established)

This investigation does **not** prove the natural-density theorem. It also does **not** construct a countersequence satisfying the full stronger package in the question. In particular, I do **not** conclude that that package is insufficient merely because the residue error below has not been estimated.

There are several checked advances over `MultiplicativeStabilityResearch.md`:

1. A finite **nonoverlapping-block mean-square lemma** gives genuine conditional Dickman distribution inside a growing dilation block, even with an arbitrary bounded weight depending on its endpoints. Its signed betweenness consequence is computed exactly; it is a telescoping rank identity, not reflection.
2. The uniform bound permits an **explicit, single-limit, same-scale reduction** with growing multipliers
   `H(X)=floor(exp(sqrt(log X)))`, `L(X)=floor(sqrt(H(X)))`.
   For every fixed pair of Lipschitz tests, the original adjacent current equals an explicit sparse-residue current plus `o(1)`. No unproved uniform-in-modulus entropy theorem or interchange of limits is used.
3. The nearby-multiplier packet used to maintain the original scale has support of density at most `L/H` and second moment at least `(1-o(1)) H/L`. This precisely identifies the loss in trying to remove its conditioning using unweighted short-interval mean squares.
4. Growing multiplicative rays retain the *entire marginal variance*. Thus extending ordinary short-interval uniformity to the transverse, growing-modulus progressions produced by these rays is actually false, including for the actual `f`.
5. The exact stability constant imposes useful rigidity on proposed countermodels. A continuous scalar reparameterization `T(f(n))` with the same Dickman marginal and the same stability bound must be `f(n)` itself. Prime-calibrated models, and bounded max-of-prime-weight models with that marginal, are also `L1`-indistinguishable from `f`.
6. The old resonant construction is explicitly ruled out by growing multipliers of size `n^0.51`, even allowing its core jitters to vary arbitrarily within their prescribed ranges.
7. A new, rigorously verifiable **near-miss** is available: a digital/core-label sequence with exact invariance under *every power of two*, Dickman marginals, all-scale short-interval uniformity (also in every fixed progression), diagonal nonconcentration, and ascent density `4/7`. It fails stability for multiplier 3. It is therefore **not** a countermodel to the all-integer hypothesis. It shows why checking growing dyadic dilations alone would not be enough.

`Submission/Spec.lean` has not been edited. The eight elementary theorems in `UniformStabilityFacts.lean` are independently kernel-checked, without importing `Submission.Spec`; their axiom reports do not contain `sorryAx`. The analytic arguments below are mathematical proofs, not claims that their asymptotic steps have been formalized in Lean.

## 1. Exact hypotheses and quantifiers

Write `P(n)=Nat.maxPrimeFac n` and, for `n>=2`,

```
f(n) = log P(n) / log n,       F(t) = rho(1/t),
F(0)=0,                       Q=F^{-1}.
```

`F` is the continuous, strictly increasing Dickman exponent CDF on `[0,1]`. Values at the finitely many initial indices will be immaterial. The target remains **ordinary** natural density of `P(n+1)>P(n)`, not logarithmic density. As recorded in the earlier note, the normalized and raw ordering signs agree for `n>=3`.

The abstract stronger package considered here is:

* **(U)** `g:N->[0,1]` and

  `|g(kn)-g(n)| <= log k / log(kn)` for every `n>=2`, `k>=1`.

* **(M)** At every scale, the empirical marginal of `g` tends to `F`.
* **(SI)** For `u(n)=phi(g(n))-integral phi dF`, with `phi` a fixed bounded continuous test,

  ```
  A_L u(m) = (1/L) sum_{r=1}^L u(m+r),
  E_L(u;Y)^2 = (1/Y) sum_{m=0}^{Y-1} |A_L u(m)|^2,

  lim_{L->infinity} limsup_{Y->infinity} E_L(u;Y) = 0.       (1)
  ```

* **(NC)**

  `lim_{eta->0} limsup_X X^{-1} #{n<=X: |g(n+1)-g(n)|<=eta}=0`.

The actual smooth cutoffs satisfy (SI), initially for cutoff tests; continuous tests follow by finite approximation. The fixed-progression variant is available too. The source checked is Tao–Teräväinen, *Value patterns of multiplicative functions and related sequences*, arXiv:1904.05096, `main.tex:214–220` (definition) and `1127–1134` (application to largest prime factors). Boundedness upgrades its averaged `L1` statement to (1). This is an all-scale **averaged-over-starting-points** assertion, not uniform distribution in every individual short interval, and its progression modulus is fixed before the limit.

For (NC), the all-scale input is Jiang–Miller, arXiv:2010.14990, lemma `thm:xdeltapn`, as detailed in the previous note. None of the new reductions assumes natural-density pair independence.

### 1.1 Verification and sharpness of (U)

Put `A=log P(n)`, `B=log n`, `c=log k`, and

```
d = max(log P(k), A)-A.
```

Then `0<=A<=B`, `0<=d<=c`, and

```
f(kn)-f(n) = (d-c A/B)/(B+c).
```

Both `d` and `c A/B` lie in `[0,c]`, proving (U). In particular,

```
log k <= delta log n  ==>  |f(kn)-f(n)| <= delta/(1+delta). (2)
```

The constant 1 in (U) is sharp: take `n` prime and `k` a power of 2 with `P(k)<=n`. Then `d=0`, `f(n)=1`, and equality holds in (U).

These are `exponent_mul_stability` and `exponent_subpower_stability` in the new Lean file. They are theorems for all integers in the stated ranges, not eventual fixed-multiplier assertions.

## 2. A positive consequence: block-interior decoupling at every scale

The following distinction matters. Short-interval control cannot automatically be restricted to a sparse set of starting points. It **can** control nonoverlapping block means, because every point of each block participates in the averaging.

### 2.1 Two finite blocking inequalities

Assume `|u|<=1`. For integers `ell,L,Y>=1`, direct comparison of shifted intervals and Jensen's inequality give

```
E_L(u;Y)
  <= sqrt(1+L/Y) E_ell(u;Y+L) + (ell-1)/L.                (3)
```

Indeed, replace `A_L u(m)` by

```
C(m) = (1/L) sum_{r=0}^{L-1} A_ell u(m+r).
```

Their difference is at most `(ell-1)/L`: shifting a length-`L` average by `s-1` costs at most `2(s-1)/L`, and then average over `1<=s<=ell`. For the mean square of `C`, use Jensen, and note that each starting point in `[0,Y+L)` occurs at most `L` times.

Consequently (1) implies, without a rate assumption,

```
E_{L(Y)}(u;Y) -> 0
whenever L(Y)->infinity and L(Y)=o(Y).                    (4)
```

First keep `ell` fixed in (3), take the limit in `Y`, and only then send `ell` to infinity. This justifies the growing short-interval lengths used below.

For nonoverlapping blocks put

```
B_K u(n) = (1/K) sum_{r=1}^K u(Kn+r),   0<=n<N.
```

The same argument gives the particularly useful **exact finite inequality**

```
[(1/N) sum_{n=0}^{N-1} |B_K u(n)|^2]^(1/2)
     <= E_ell(u;NK) + (ell-1)/K.                         (5)
```

There is no factor `sqrt(K)` on the right. Thus the left side tends to zero for **any** `K=K(N)->infinity`, with `N->infinity`. Changing the block indices to `1<=n<=N` changes only one block at either endpoint.

For the abstract continuous-test formulation of (SI), cutoff tests follow by continuous majorants/minorants, (M), and continuity of `F`. Applying (5) to a finite grid of cutoff tests, using monotonicity of empirical CDFs and uniform continuity of `F`, proves

```
(1/N) sum_{n=1}^N sup_t
 | (1/K) #{1<=r<=K: g(Kn+r)<=t} - F(t) | -> 0.            (6)
```

All limits here are ordinary, all-scale limits.

### 2.2 Conditional interior distribution really follows

Let `K(N)->infinity`. An arbitrary bounded block weight `W_N(n)`, even one depending on both boundary values or on the entire sequence, can be inserted in (6): the error remains bounded by the unweighted mean absolute discrepancy.

In particular, if `log K=o(log N)`, (U) also replaces the boundary values `g(Kn),g(K(n+1))` by `g(n),g(n+1)` outside an `o(N)` initial set. For bounded continuous `A:[0,1]^2->R` and `b:[0,1]->R`,

```
(1/N) sum_{n<=N} A(g(n),g(n+1))
    [(1/(K-1)) sum_{r=1}^{K-1} b(g(Kn+r)) - integral b dF]
       -> 0.                                            (7)
```

In fact (7), written with the original endpoints, already follows from (6); (U) permits either choice of endpoints. The assertion holds simultaneously for any fixed number of independently sampled interior positions, sampled with replacement: the conditional empirical product is a product of block means. No pair-law limit has to be assumed in order to state (7).

This is genuine endpoint/interior decoupling. It is stronger than merely saying that the unweighted marginal at scale `KN` is Dickman.

### 2.3 Its signed betweenness consequence is a gradient, not reflection

Put `s_n=sgn(g(n+1)-g(n))` and

```
V_K(n) = (1/(K-1)) #{1<=r<K:
  min(g(n),g(n+1)) < g(Kn+r) < max(g(n),g(n+1))}.
```

Uniformity in the threshold in (6), with endpoint atoms handled by continuity of `F`, gives

```
(1/N) sum_{n<=N}
 |V_K(n)-|F(g(n+1))-F(g(n))|| -> 0.
```

It follows that

```
(1/N) sum_{n<=N} s_n V_K(n)
 = (1/N) sum_{n<=N} [F(g(n+1))-F(g(n))] + o(1)
 = o(1).                                                (8)
```

This does **not** imply `(1/N)sum s_n ->0`. Any coupling with equal marginals, including a nonexchangeable coupling, satisfies the rank-gradient identity on the right. For example, `Q(U), Q(U+1/3 mod 1)` has ascent probability `2/3`; adjoining any number of independent Dickman interior variables satisfies all the endpoint/interior factorization identities just used.

Thus using uniform block histograms in the triangle/betweenness identity does produce a valid estimate, but the checked estimate is (8), not the missing signed bypass estimate for the original adjacent current.

## 3. A single-limit common-scale growing-dilation formula

Here is a version of the nearby-large-dilation route that genuinely uses the new uniform bound. Unlike the previous fixed-parameter lemma, all parameters below may grow with the original counting scale.

Take fixed Lipschitz `phi,psi:[0,1]->[0,1]`, and set

```
u(n)=phi(g(n))-integral phi dF,
v(n)=psi(g(n))-integral psi dF,
C = Lip(phi)+Lip(psi),
j_q(m)=u(m)v(m+q)-v(m)u(m+q),
J_q(Y)=(1/Y)sum_{1<=m<=Y}j_q(m).
```

In particular `|u|,|v|<=1`, `|j_q|<=2`. Centering affects the corresponding uncentered current only by endpoints.

For integers `X>=4`, `H>=1`, `1<=L<=H`, let `Y=HX` and define

```
B_q(Y) = (q/Y) sum_{1<=m<=Y, q|m} j_q(m),

R(X;H,L) = (1/L) sum_{q=H+1}^{H+L} [B_q(Y)-J_q(Y)]
 = (1/(YL)) sum_{m<=Y} sum_{q=H+1}^{H+L}
           (q 1_{q|m}-1) j_q(m).                         (9)
```

Notice the normalization `q/Y`. The number of multiples is `floor(Y/q)`, not `X`.

### 3.1 Finite estimate, with all scales and floors retained

Under (U),

```
|J_1(X)-R(X;H,L)|
 <= E_L(u;Y)+E_L(v;Y)
       + 4L/H + 4C log(2H)/log X + 32/sqrt(X).            (10)
```

**Proof.** Put `M_q=floor(Y/q)`. Since `q<=2H`, `M_q>=X/4`. For `n>=sqrt(X)`, (U) at both endpoints gives an exponent displacement at most

```
eta = log(2H)/(0.5 log X + log(2H)) <= 2 log(2H)/log X.
```

The corresponding change in `j` is at most `2C eta`. The `n<sqrt(X)` terms cost at most `16/sqrt(X)` in the normalized average. Also `0<=1-qM_q/Y<q/Y<=2/X`. Hence

```
|B_q(Y)-J_1(M_q)| <= 2C eta + 16/sqrt(X) + 4/X.
```

For a prefix average of a 2-bounded sequence,

```
|J_1(M_q)-J_1(X)| <= 4(X-M_q)/X <= 4L/H+4/X.
```

On the other hand, averaging the **unconditioned** currents gives exactly

```
(1/L)sum_{r=1}^L J_{H+r}(Y)
 = (1/Y)sum_{m<=Y}
     [u(m) A_L v(m+H) - v(m) A_L u(m+H)].                 (11)
```

Cauchy–Schwarz bounds this by the two short-interval mean-square norms. Replacing the starting range `H+1,...,Y+H` by `0,...,Y-1` costs at most `2 sqrt((H+1)/Y) <= 2 sqrt(2/X)` in the sum of the two norms. Combining these inequalities gives (10); the constant 32 safely covers these endpoint costs. QED.

### 3.2 Explicit growing choices, not a hidden diagonal subsequence

Choose once and for all

```
H(X) = floor(exp(sqrt(log X))),
L(X) = floor(sqrt(H(X))).                                (12)
```

Both grow, `L/H->0`, `log H/log X->0`, and `L=o(HX)`. Equations (4) and (10) prove the all-scale identity

```
J_1(X) - R(X;H(X),L(X)) -> 0.                            (13)
```

No quantitative rate in the short-interval theorem is required. In particular, no assertion valid only for fixed `q` has been applied at `q=q(X)`.

For comparison, `H=floor(X^delta)`, `L=floor(sqrt(H))` gives

```
limsup_X |J_1(X)-R(X;H,L)| <= 4C delta.                   (14)
```

One may send `delta` to zero afterwards, but (12) avoids even that extra parameter.

**Exact remaining target.** Proving

```
R(X;H(X),L(X)) -> 0                                     (15)
```

for every fixed pair of Lipschitz tests would give pair reflection at the original natural scale, by (13). Bounded continuous product tests follow by approximation. Near-diagonal nonconcentration then allows the ordering test and yields natural ascent density `1/2`.

Conversely, vanishing of these adjacent antisymmetric product currents implies (15), by the same identity (13). Thus (15) is not a proved consequence or a heuristic independence statement: it is a precise surviving signed estimate. This investigation does not establish (15).

## 4. Why unweighted mean squares do not remove the packet conditioning

This is a quantitative issue, not just a missing word such as “equidistributed.” For the same `Y=HX` define

```
S = {m<=Y: some q in [H+1,H+L] divides m},
D(m)=(1/L) sum_{q=H+1}^{H+L} q 1_{q|m}.
```

Then the following bounds are elementary and finite:

```
|S|/Y <= L/H,
1-2/X <= (1/Y)sum_{m<=Y}D(m) <= 1,
(1/Y)sum_{m<=Y}D(m)^2 >= (1-2/X)^2 H/L.                  (16)
```

The last inequality is Cauchy–Schwarz on `S`. With `L/H->0`, the normalized sampling weight has diverging second moment, rather than approximating 1 in mean square. Both endpoints of every sampled edge are multiples of its `q`; apart from the harmless final extension by `2H`, both belong to this sparse union.

There is also an exact insensitivity estimate. If two 1-bounded sequences differ only on a set `S`, then

```
(1/Y)sum_{m<Y}|A_L u(m)-A_L v(m)|^2
 <= 4 |S intersect [1,Y+L]|/Y.                           (17)
```

Indeed the difference is at most twice the proportion of `S` in the interval; square this using that this proportion is at most 1, and double-count. Global marginals and unit-gap diagonal-strip counts likewise change by at most the density of `S`, and twice that density, respectively, up to endpoints.

Thus the *unweighted* inputs by themselves can be insensitive to the packet's sampled endpoints while the conditioned statistic is of order 1. Equations (16)–(17) explain why applying Cauchy–Schwarz and then discarding the residue condition is not legitimate.

**Important qualification:** modifying values on `S` arbitrarily generally destroys (U) for other multipliers. These estimates do **not** constitute a full-package countermodel. An argument coupling (U) to this residue geometry might still prove (15); no such argument has been completed here.

## 5. Two other checked consequences for proposed dilation arguments

### 5.1 Multiplicative rays do not satisfy the proposed transverse mean-square conclusion

Let `phi` be a nonconstant Lipschitz test under `F`, with variance `sigma_phi^2>0`, and let `u=phi(g)-integral phi dF`. Take any `K(X)->infinity` with `log K=o(log X)`. For `X<=n<2X`, (U) implies

```
|(1/K)sum_{k=1}^K u(kn)-u(n)|
 <= Lip(phi) log K/log X.
```

Using (M) on `[X,2X)`, this proves

```
(1/X)sum_{X<=n<2X}|(1/K)sum_{k=1}^K u(kn)|^2
      -> sigma_phi^2,                                   (18)
```

not zero. For `K<=X^delta`, the limiting lower bound for the square-root mean square is at least `sigma_phi-Lip(phi) delta/(1+delta)`.

This holds for the actual `f`. The progressions here have growing modulus `n` and small cofactor length `K`; they are not the fixed-modulus progressions covered by the known short-interval theorem. Stability actually preserves fluctuations on these progressions. It cannot be used as a justification for applying ordinary short-interval mean-square cancellation along them.

### 5.2 Direct small-multiplier endpoint reflection has a square-root barrier

Suppose positive integers satisfy

```
a n = b(m+1),       c(n+1)=d m,
1<=a,b,c,d<=K.
```

Eliminating `m` gives

```
(ad-bc)n = b(c+d).                                      (19)
```

The determinant is a positive integer. Therefore

```
n <= b(c+d) <= 2K^2.                                    (20)
```

In particular, an exact matching of both endpoints in reversed order cannot use only multipliers `<=X^delta` for `n asymp X` and fixed `delta<1/2`. This is not a theorem excluding averaging or more elaborate paths; it rules out the direct two-product reflection coupling. Equations (19)–(20) are kernel-checked as `small_multiplier_reflection_barrier`.

## 6. Rigidity tests for stronger countermodels

### 6.1 Prime calibration, or max-of-prime weights, leaves no independent model

Let `g` satisfy (U). Applying it with the prime divisor `p=P(n)` as base yields

```
g(n) >= g(P(n))-1+f(n).                                 (21)
```

Hence if `g(p)=1` for every prime, then `g(n)>=f(n)` for all `n>=2`. This pointwise statement is kernel-checked in `prime_calibrated_domination`.

If in addition `g` has the same limiting marginal `F`, its limiting mean equals that of `f`. Consequently

```
(1/X)sum_{n<=X}|g(n)-f(n)| -> 0.                         (22)
```

The same conclusion holds if `g(p)->1` along the primes. Indeed `P(n)->infinity` in natural-density probability, so the mean of `1-g(P(n))` tends to zero; (21) controls the negative part, and equality of the limiting means controls the positive part.

There is an opposite-sided rigidity for models of the form

```
g(n) = max_{p|n} w(p) / log n,     0<=w(p)<=log p.
```

Such models satisfy (U), but also `g(n)<=f(n)`. Equality of the limiting marginal again forces (22).

By the actual diagonal nonconcentration theorem, (22) forces equality of the limiting adjacent ordering currents whenever either is being tested. More explicitly, for any `eta>0`,

```
|a_g(X)-a_f(X)|
 <= (4/(eta X)) sum_{n<=X+1}|g(n)-f(n)|
       + (2/X)#{n<=X: |f(n+1)-f(n)|<=2eta}.              (23)
```

First send `X` to infinity and then `eta` to zero. Thus a countermodel in either class would not be an independent abstract obstruction: it would also settle the actual arithmetic question in the same direction.

### 6.2 Continuous scalar reparameterizations are completely rigid

Suppose `T:[0,1]->[0,1]` is continuous and `g(n)=T(f(n))` satisfies (U). Growing prime and power-of-two multipliers imply the following metric bound:

```
|T(y)-T(x)| <= min(y, 1-x/y)     (0<=x<y<=1).             (24)
```

Here is the realization argument, rather than assuming that `f` is an arbitrary real variable.

* To obtain `1-x/y`, take `n_j=2^{a_j}p_j`, with primes `p_j->infinity` and `a_j` chosen so `f(n_j)->y`. Multiply by powers of 2 so that `f(k_j n_j)->x`. The stability right side tends to `1-x/y`.
* To obtain `y`, first arrange `f(n_j)->x` in the same way. For `y<1`, choose a prime `k_j` with `log k_j / log n_j -> y/(1-y)`. Bertrand's postulate suffices. This prime exceeds `P(n_j)` eventually, so `f(k_j n_j)->y`, and the stability right side tends to `y`.
* Endpoint cases follow by continuity; the bound `y=1` in the second construction is trivial.

If `T` has full image `[0,1]`, take preimages of 0 and 1 and order them as `x<y`. Equation (24) gives `1<=y<=1`, and then `1<=1-x`, so these preimages must be the endpoints 0 and 1. Applying (24) to the endpoint pairs now gives

```
T(t)=t for every t,       or       T(t)=1-t for every t.  (25)
```

This metric-to-rigidity deduction is kernel-checked as `scalar_metric_rigidity`.

If `T(f(n))` has the Dickman marginal, continuity and full support of `F` ensure that `T` has full image. The reflection alternative does not preserve `F`, since

```
F(1/2)=1-log 2 != 1/2.
```

Therefore `T` is the identity. In particular, starting from the actual `f`, a nonmonotone measure-preserving reparameterization cannot supply an abstract countermodel with (U).

## 7. An explicit exclusion of the old resonant construction

This section checks a concrete growing multiplier obstruction, including its bounded jitters, rather than just asserting that it violates (U).

In the old pure phase, with `eta=1/100`, `beta=1/1000`, values have the form

```
g(m)=Q(h_beta({tau log m + W_m})),    |W_m|<=eta/2,
```

where `h_beta` rises linearly from 0 to 1 on `[0,1-beta]` and resets on the remaining interval. The argument below allows the `W_m` to vary arbitrarily; no probabilistic assertion about them is needed.

Set `n=floor(tau)`, `K=floor(tau^(51/100))`. The old phase lasts throughout all `nk` with `K<=k<=2K`, by its frequency-separation choices. For every fixed nonzero Fourier frequency, the second derivative estimate gives

```
(1/K)sum_{K<=k<=2K} e(h tau log k)
  <<_h sqrt(tau)/K + 1/sqrt(tau) -> 0.                    (26)
```

Thus the unjittered phases are equidistributed as `k` varies. Put

```
gamma=eta/(1-beta)=10/999.
```

There are `k` for which every allowed jitter leaves the tent value at most `gamma+o(1)`, and others for which it is at least `1-gamma-o(1)`: use small phase intervals lying wholly inside the rising branch, just above 0 and just below `1-beta`.

For the Dickman transform we have the rigorous lower bound

```
rho(10/3) >= 2/9 + log 3 - (17/9)log 2 > 0.01155 > gamma. (27)
```

To verify it, use `log u >= 2(u-1)/(u+1)` on `[1,2]` in

```
rho(3)=1-log 3 + integral_2^3 log(t-1)/t dt
      >= 1/3+log(3/4),
```

and then `rho(10/3)>=rho(3)-rho(2)/9`. Therefore `Q(gamma)<3/10`; also `Q(1-gamma)=exp(-gamma)>=1-gamma`. The range of the values on these multiples has limiting diameter at least

```
1-gamma-3/10 > 0.68998.                                 (28)
```

But (U), comparing each multiple to the same base `n`, would bound that diameter by

```
2 log(2K)/log(2Kn) -> 102/151 < 0.67550.                 (29)
```

The strict gap is more than `0.01449`. Thus the old resonant/jitter construction cannot satisfy (U). The comparison (27)–(29) is certified with rational logarithm bounds in the verification script.

This excludes this mechanism, not every possible arithmetic countermodel.

## 8. A new near-miss countersequence: exact growing dyadic stability plus (M), (SI), (NC)

This is an actual deterministic-sequence existence result. It is **not** a counterexample to the requested stronger package: multiplier 3 fails, as explicitly checked below. In particular it cannot replace the missing all-integer hypothesis in a negative conclusion.

For a positive integer `n`, let `r(n)` be its odd part and `t(n)` the sum of its binary digits modulo 3, valued in `{0,1,2}`. Choose independent uniform labels `U_r` on `[0,1]`, indexed by positive odd integers, and define

```
G(n)=(t(n)+U_{r(n)})/3,       g(n)=Q(G(n)).               (30)
```

There is a deterministic realization with the following properties:

* `g(2^a n)=g(n)` for every `a>=0,n>=1` — exact stability for arbitrarily large dyadic multipliers;
* the marginal is `F` at all scales;
* (SI) holds at all scales, also for every fixed arithmetic progression;
* (NC) holds;
* the ordinary ascent density is exactly `4/7`, with signed mean `1/7`.

Here are the details needed to justify all these assertions.

### 8.1 Marginals and short intervals

For `zeta=exp(2 pi i/3)`, the binary product identity gives

```
sum_{0<=n<2^a} zeta^{h t(n)}=(1+zeta^h)^a,    h=1,2.
```

The modulus is 1. Every interval of length `L` decomposes into at most `2(log_2 L+1)` aligned dyadic blocks. Thus the three digit-sum classes have discrepancy `O(log(2L))` in **every** such interval, uniformly in its position.

For a cutoff `s`, the expected indicator in (30), conditional on `t(n)=j`, is

```
b_j(s)=min(1,max(0,3F(s)-j)),
(1/3)sum_{j=0}^2 b_j(s)=F(s).
```

If a length-`L` interval starts beyond `L`, its integers have distinct odd parts: two with the same odd part have ratio at least 2. The labels in that interval are therefore independent. Its centered cutoff mean has expected square

```
<= 1/(4L) + O(log(2L)^2/L^2),                            (31)
```

uniformly in the starting point. This proves the required short-interval estimate after the deterministic-realization step below.

For completeness, fixed progressions can be treated by the same elementary Fourier argument. For any fixed modulus `q`, additive-character filtering reduces the relevant digit sums on a progression to products

```
product_{j=0}^{a-1} (1+zeta^h e(ell 2^j/q)).
```

The orbit of `2^j ell/q` is eventually periodic. No eventual cycle can have every factor of modulus 2: that would require all its phases to equal `-h/3`, incompatible with doubling when `h=1,2`. For fixed `q` these products are consequently `O_q(2^{(1-c_q)a})` for some `c_q>0`. Dyadic decomposition gives uniform discrepancy `O_q(L^{1-c_q})` in fixed progressions. When the starting point exceeds `qL`, their labels again have distinct odd parts. This gives (31) with a decaying `O_q(L^{-2c_q})` term in place of its last term.

### 8.2 Diagonal nonconcentration and the exact current

Except at the initial pair `1,2`, adjacent integers have distinct odd parts. Conditional on their digit-sum classes, their `G` values are independent, with densities at most 3. Hence

```
Pr(|g(n+1)-g(n)|<=eta) <= 6 omega_F(eta),                 (32)
```

where `omega_F(eta)=sup_{|x-y|<=eta}|F(x)-F(y)| ->0`.

To compute the current, write `v_2(n+1)=r`. Then uniquely

```
n=2^(r+1)m+2^r-1,
t(n)=t(m)+r mod 3,          t(n+1)=t(m)+1 mod 3.
```

For each fixed `r`, `t(m)` is uniformly distributed, and this valuation class has density `2^(-r-1)`. A forward three-cycle has signed ordering mean `1/3`; its inverse has mean `-1/3`; equal bins have mean 0 after averaging their independent labels. The masses of `r mod 3 = 0,1,2` are respectively `4/7,2/7,1/7`. Therefore

```
lim_X (1/X)sum_{n<=X} E sgn(g(n+1)-g(n))
   = (1/3)(4/7-1/7)=1/7.                               (33)
```

First truncate `r` at a fixed value and then let that value grow; its omitted density is at most a geometric tail. There are no ties almost surely outside the initial pair, giving ascent density `(1+1/7)/2=4/7`.

### 8.3 A deterministic realization, at all scales

The number of odd-core collisions obeys

```
#{n,m<=N: r(n)=r(m)}
 <= N sum_{a,b>=0} 2^(-max(a,b)) = 6N.                   (34)
```

A bounded statistic involving any fixed finite set of shifts has variance `O(N)` for its sum up to `N`: two such statistics are independent unless a pair of their core labels collides, and (34) bounds every shifted collision count. The implied constant can depend on the fixed shifts.

Apply Chebyshev on the grid `N=j^2`. Its failure probabilities are summable for every fixed positive tolerance. Borel–Cantelli and interpolation between successive squares give empirical average minus expected average tending to zero at **every** scale, simultaneously for a countable list containing rational marginal cutoffs, the sign statistic, rational-width diagonal strips, and every fixed-length/fixed-progression mean-square statistic. Equations (31)–(33) therefore hold for one deterministic realization. Continuity and monotonicity extend from rational tests as necessary.

### 8.4 Exactly why it is not the requested countermodel

For `n=2^a`, the two values

```
g(n)=Q((1+U_1)/3),       g(3n)=Q((2+U_3)/3)
```

have a fixed, strictly positive difference almost surely. But `log 3/log(3*2^a)->0`. Thus even the fixed multiplier 3 violates (U), not just a very large multiplier.

This near-miss demonstrates that combining short-interval mixing and diagonal nonconcentration with **only growing dyadic invariance** would give a false theorem. It does not establish insufficiency when *all* multipliers are imposed. It also does not have the logarithmic half-density conclusion, so it is not a replacement for the earlier qualitative-all-multiplier model.

## 9. Entropy-decrement quantifiers: the diagonal still needs a new estimate

The entropy statement in Tao–Teräväinen arXiv:1809.02518, Proposition `eda` (`1809.02518.tex:409–421`), bounds

```
sum_{m in exceptional_set(d)} 1/m <= C_epsilon
```

uniformly in the scale parameter `d`. This is not an estimate along a varying diagonal such as `d=2^{-m}`, which is what a common original scale asks for when the lifted scale changes with the multiplier size.

A precise quantifier counterexample is

```
E_d(m)=1_{|log_2 d+m|<1/4}.
```

For each `d` there is at most one bad integer `m>=1`, so its weighted exceptional mass is at most 1, uniformly in `d`. Nevertheless `E_{2^{-m}}(m)=1` for every `m`. The indicator may be replaced by a continuous triangular bump with uniformly bounded Lipschitz constant in `log d` without changing this conclusion.

This is not an arithmetic countermodel; it proves only that the stated entropy exceptional-set bound cannot be specialized to the desired diagonal. Uniform stability controls the *dilation error* for growing multipliers, as (10) shows. It does not, just by substitution, make the entropy/residue decoupling error uniformly small on that diagonal.

## 10. What the investigation leaves as an actual proof route

For the actual exponent function, (13) is unconditional and uses precisely the stronger stability and all-scale short-interval package. A proof of the antisymmetric packet estimate (15), for the explicit subpower parameters (12), would therefore be a genuine ordinary-density proof route, not a logarithmic-average route. Only fixed Lipschitz product tests are needed; diagonal nonconcentration handles ordering at the end.

The remaining task is genuinely to bound this **signed**, residue-conditioned two-point statistic. Ordinary short-interval distribution, block-interior decoupling, and the existing entropy exceptional-set statement do not themselves supply that estimate in the derivations checked here. The rigidity tests sharply restrict several natural countermodel attempts, but they do not classify every sequence satisfying (U).

Accordingly, both of the following remain unresolved in this work:

* proving pair reflection from the entire all-integer stronger package;
* constructing a nonreflective deterministic sequence satisfying that entire package.

There is no claimed completion, disproof, or weakening of the Lean target.

## Verification record

* `lake env lean Submission/UniformStabilityFacts.lean` succeeds. All eight printed axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
* `UniformStabilityVerification.py` checks finite blocking identities, the sparse-packet support and second-moment inequalities with rational arithmetic, the logarithm certificate in (27)–(29), the dyadic digital-current formula on finite prefixes, and the largest-prime-factor bound for 599,500 variable-multiplier pairs.
* The script also checks the floor normalizations in the common-scale formula on finite examples. Such numerical tests are sanity checks, not proofs of an asymptotic estimate for (15).
* The original `Spec.lean` SHA-256 remains `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

## 11. Exact metric form of (U) and an arbitrary-chain transport obstruction

This section was independently checked after the earlier investigation. It does **not** resolve the full statistical implication in section 10.

For integers a,b>=2 define

```
d(a,b) = 1 - log(gcd(a,b))/log(lcm(a,b)).
```

This is a metric: represent an integer by its prime-power slots (p,j),
1<=j<=v_p(n), with slot weight log p. The displayed formula is weighted
Jaccard distance. To prove its triangle inequality directly, assign
independent exponential clocks with these rates to the finitely many slots
in three integers. The earliest slot H(A) of a nonempty set A satisfies
Pr(H(A)!=H(B))=d(A,B): the first clock in A union B is in their intersection
exactly when the two earliest slots agree. The triangle inequality for
indicators of disagreement, followed by expectation, proves the assertion.
Positivity, symmetry, and separation follow immediately from the formula.

For any g on integers >=2, (U) is equivalent to

```
|g(a)-g(b)| <= d(a,b) for all a,b>=2.                   (35)
```

Indeed, apply (U) on each of the edges a -> lcm(a,b) <- b. The sum of
these two edge costs is exactly d(a,b), using
log a+log b=log gcd(a,b)+log lcm(a,b). Conversely when a divides b,
d(a,b)=log(b/a)/log b, recovering (U).

In particular, every chain of multiplication/division edges from a to b
has total (U)-cost at least d(a,b), and the two-edge lcm chain attains
this cost. Arbitrarily long chains cannot reduce that pointwise bound.
For a fixed b the distance function g_b(a)=d(a,b) satisfies (U) and
attains equality against b. This last sharpness assertion is not a
statistical countermodel with diagonal nonconcentration.

### Reversing adjacent pairs costs a fixed amount

For n,m>=2 set

```
r = max(d(n,m+1), d(n+1,m)),
G0 = gcd(n,m+1), G1 = gcd(n+1,m),
T = log(n(n+1)m(m+1)), B = log(n+m+1).
```

Both nm and (n+1)(m+1) are divisible by G0*G1. Consequently

```
G0*G1 divides n+m+1, and G0*G1 <= n+m+1.                (36)
```

Rearranging each inequality d<=r yields
log G0 >= ((1-r)/(2-r))log(n(m+1)) and its other-endpoint counterpart.
Sum these and use (36). Since T>B, the resulting bound is

```
r >= (T-2B)/(T-B).                                    (37)
```

Uniformly for n,m in [cX,X], with c>0 fixed, this gives

```
r >= 2/3 - O_c(1/log X).                              (38)
```

The constant is sharp: take n=t(t+2), m=t^2-1. The two gcds are
t*gcd(t,2) and (t+1)*gcd(t-1,2); both distances tend to 2/3.

Even allowing arbitrary destination scales, uniformly as min(n,m)->infinity,

```
r >= 1/2 - O(1/log min(n,m)).                         (39)
```

By symmetry suppose m>=n and put a=log n,b=log m. If b>=2a,
d(n,m+1)>=1-a/log(m+1)>=1/2. Otherwise T>=2(a+b) and
B<=b+log 3; monotonicity of (T-2B)/(T-B), for n>3, gives
r >= (2a-2log 3)/(4a-log 3). Sharpness follows from m=n^2-1:
the distances are 1/2 and log(n-1)/log(n^2-1), respectively.

For a coupling of uniform indices in {2,...,X}, at least 1-2c-O(1/X)
of its mass has both indices >=cX. Applying (38), then letting X grow
and c decrease to zero, proves an expected maximum endpoint cost of
at least 2/3-o(1). Thus randomized matching does not remove the
pointwise transport obstruction either.

**Logical limit:** d is the sharp cost of *certifying* closeness using
(U), not a lower bound on |g(a)-g(b)| for a particular g. A scalar g may
collapse very distant arithmetic points. These inequalities rule out a
vanishing-cost reflection matching based only on multiplication/division
chains; they neither disprove statistical reversibility under (U) nor
settle the actual largest-prime-factor conjecture.
