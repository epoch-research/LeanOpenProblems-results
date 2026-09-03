# Erdős 371: quantitative near-comparison bounds by a Fourier-positive sieve

## Status and actual conclusions

**The natural-density conjecture is not proved or disproved here.** No declaration in `Spec.lean` is used. No Lean file is modified. This note proves quantitative estimates for the actual largest-prime-factor function, not a countermodel or an equivalence with the conjecture.

Write `P(1)=1`, `L=log X`, and

```
N_X(delta) = #{1 <= n < X : |log P(n+1)-log P(n)| <= delta L}.
```

### Theorem A (uniform near-comparison estimate)

For every `0<epsilon<1`, there are constants `C_epsilon,X_epsilon` such that, for all integers `X>=X_epsilon` and **all** `0<=delta<=1/100`,

```
N_X(delta) <= C_epsilon X [delta + (log X)^(-1+epsilon)].       (A)
```

Thus, for every fixed `R>1`,

```
#{n<X : R^(-1) <= P(n+1)/P(n) <= R}
    <<_(R,epsilon) X/(log X)^(1-epsilon).                     (A1)
```

In particular the upper natural density of a fixed-width normalized diagonal strip is `O(delta)`, rather than the `O(delta^(1/3))` deduction recorded in `ReflectionResearch.md`. The constants in (A) are not explicit. This is a deduction from established dispersion and upper-sieve estimates; no literature-priority claim is made.

### Theorem B (a quantitative signed sector)

Fix `1/2 < beta < 17/33`, and put

```
I_X = {p prime : sqrt X < p <= X^beta},
s(n) = sgn(P(n+1)-P(n)).
```

Then, for every `0<epsilon<1`,

```
|sum_(1<=n<X) s(n) 1_{min(P(n),P(n+1)) in I_X}|
    <<_(beta,epsilon) X/(log X)^(1-epsilon).                  (B)
```

This is a signed ordinary-count estimate, uniform through the ordering cutoff, not merely a fixed exponent-rectangle result. It does not control the complementary sectors.

The two extra devices are:

1. small-prime extraction can be made uniform in **every** bounded function `h(P(m))`, even though it is not generally multiplicative;
2. a triangular majorant of `|u-v|<=delta` has a nonnegative Fourier transform of total mass 2, independently of delta. Hence there is no loss of `1/delta` from a cutoff grid.

## 1. Precisely used analytic inputs

The non-elementary estimates used below are:

* Fouvry--Radziwiłł, *Level of distribution of unbalanced convolutions*, arXiv:1811.08672, `/corpus/src/1811.08672/FouvryRadzi7.tex`, Corollary `cor:Main(i)`, lines 64--78. For divisor-bounded coefficients `alpha_m,beta_n`, with the short coefficient Siegel--Walfisz, it gives arbitrary logarithmic savings in the sum of absolute progression discrepancies over `Q<q<=2Q`, on `t<mn<=2t`, provided
  ```
  exp((log t)^eta) <= N <= Q^(-11/12) t^(17/36-eta).
  ```
  The residues used here are just `+1` and `-1`. The long coefficient can be an arbitrary bounded complex sequence. Its dependence on X or on a Fourier frequency costs nothing.
* The prime Siegel--Walfisz theorem, uniformly for an interval truncated at arbitrary endpoints.
* Shiu's upper bound for divisor-bounded nonnegative multiplicative functions; the needed statement is also `le:shiu`, lines 309--315 of that source:
  ```
  sum_(x-y<=m<=x, m=a mod q) g(m)
    <<_(k,eta) y/phi(q) prod_(ell<=x) [1+(g(ell)-1)/ell],
  ```
  if `0<=g<=tau_k`, `(a,q)=1`, `x^eta<=y<=x`, and `q<=y x^(-eta)`.
* The ordinary two-dimensional Selberg upper-bound sieve, applied to two primitive linear forms with determinant 1. Its exact use and local factors are given in Section 5.
* Chebyshev's prime upper bound, Mertens' prime product estimate, and Brun--Titchmarsh for the short prime cells in Section 2.

There is no assumed asymptotic for two primes at affine forms, no natural pair-independence hypothesis, and no use of a logarithmic-density theorem.

## 2. A largest-factor test estimate uniform in the test function

For a bounded function `h` on `{1} union {primes}` and `r=+1,-1`, define

```
E_p(h;r) = sum_(m<=X, m=r mod p) h(P(m))
           - 1/(p-1) sum_(m<=X, (m,p)=1) h(P(m)).
```

### Lemma 1

Fix `1/2<beta<17/33`. For each `epsilon>0`,

```
sum_(sqrt X<p<=X^beta) |E_p(h;r)|
    <<_(beta,epsilon) X L^(-1+epsilon),                     (1)
```

uniformly over **all** `|h|<=1`. The function h is the same for all p, but may depend arbitrarily on X and on another parameter.

#### Proof

Choose a fixed `0<sigma<min(epsilon/4, (17/33-beta)/100, 1/10)`, and set

```
U=exp(L^sigma),   V=exp(L^(1-sigma)).
```

First replace h by `h_>(q)=h(q)1_{q>V}`. Rankin's elementary bound gives

```
Psi(X,V) << X log V exp(-L/log V)
         = X L^(1-sigma) exp(-L^sigma).                    (2)
```

For completeness, use the Rankin exponent `1-1/log V`. The Euler product is `O(log V)`: the extra prime sum is bounded by
`(e-1)(log V)^(-1) sum_(ell<=V) log ell/ell=O(1)`, and the prime-power tail is bounded. Thus (2) is smaller than `X/L^A` for every fixed A.

Every `m>=2` is in at most two of the progressions `m=+1 mod p` (or `m=-1 mod p`) with `p>sqrt X`, since their primes divide the positive integer `m-1` (or `m+1`) of size at most `X+1`. The exceptional `m=1` in the `+1` progressions contributes at most `#I_X<=X^beta`. Also

```
sum_(p in I_X) 1/(p-1) = O_beta(1).                        (3)
```

It follows that replacing h by `h_>` changes the left side of (1) by `O(Psi(X,V)+X^beta)`, negligible to every fixed logarithmic order.

Discard `m<=X/L^K`, with a fixed sufficiently large K. Direct progression counting bounds the aggregate error by

```
O((X/L^K) sum_(p in I_X) 1/p + #I_X + (X/L^K) sum 1/(p-1))
  = O_beta(X/L^K+X^beta).                                  (4)
```

Split the remaining range into dyadic intervals `t<m<=2t`; throughout, `log t~L`. Partition `(U,V]` into prime cells of relative width comparable to `Delta=L^(-B)`, for a sufficiently large fixed B. An integer m is good when it has a prime in `(U,V]` and the **first occupied cell contains exactly one prime factor, counted with multiplicity**. If that prime is a, the factorization

```
m=a b
```

is unique; b has no prime factor in `(U, upper endpoint of that cell]`. Since `a<=V`,

```
h_>(P(ab)) = h_>(P(b)).                                    (5)
```

For each cell the good contribution is therefore a convolution of the ordinary prime indicator on that cell with an arbitrary 1-bounded coefficient in b. This is where arbitrary h is permitted; no Siegel--Walfisz assertion about `h(p)` is used.

Apply Fouvry--Radziwiłł to these convolutions. The number of cells and localization intervals is polynomial in L. Take its short-factor parameter to be, for example, `eta=sigma/2`. For Q in the required range the fixed positive margin

```
17/36-(11/12) beta > 0                                    (6)
```

ensures that `N<=V=t^(o(1))` satisfies the upper condition; `N>=U/2` satisfies the lower condition. All moduli can be split into dyadic blocks. Arbitrary logarithmic savings absorb the polynomial number of cells/blocks. Consequently the good part of (1) is `O_A(X/L^A)` for every fixed A, uniformly in h.

The bad contribution is bounded pointwise in p, using only `|h|<=1`:

```
# {t<m<=2t : m=r mod p, m bad}
  << t/(p-1) [L^(-1+2 sigma)+L^(1-B)].                     (7)
```

Here are details for (7). For no prime factor in `(U,V]`, Shiu applied to the exclusion indicator gives a prime product `O(log U/log V)=O(L^(-1+2 sigma))`. For two primes a,b in a common cell, use the elementary count `O(t/(pab))`; its rounding term is absorbed because `p V^2<t` for large X. This includes repeated primes. Brun--Titchmarsh gives `sum_(a in a cell)1/a=O(L^(-B))`, and there are `O(L^(B+1))` cells. Summing their squared reciprocal sums gives `O(L^(1-B))`. The coprime principal mean has the same bound, by taking modulus 1 and dividing by p-1.

Sum (7) using (3), then sum the t-intervals geometrically. Choose `2 sigma<epsilon` and B,K sufficiently large. Equations (2)--(7) prove (1). In particular its constant is independent of any oscillation of h. ∎

## 3. Fourier-positive treatment of the central diagonal

Fix `beta=51/100`; it satisfies (6), with exact margin `17/3600`. Let

```
Phi_delta(v)=2(1-|v|/(2 delta))_+       (delta>0).
```

It is nonnegative, supported on `|v|<=2 delta`, and at least 1 on `|v|<=delta`. With Fourier convention `e(t)=exp(2 pi i t)`,

```
Phi_delta(v) = integral_R e(tv) w_delta(t) dt,
w_delta(t)=4 delta [sin(2 pi delta t)/(2 pi delta t)]^2 >=0,
integral_R w_delta(t)dt=2.                                (8)
```

The value at t=0 is by continuity. The last equality also follows from the convolution of two intervals. The integral is absolutely convergent.

Consider

```
T_r = sum_(p in I_X) sum_(m<=X, m=r mod p)
        1_{P(m)>sqrt X} Phi_delta((log P(m)-log p)/L).
```

Apply Lemma 1 for every real t with

```
h_t(q)=1_{q>sqrt X} e(t log q/L),  a_t(p)=e(-t log p/L).
```

All these functions are 1-bounded. Multiply by `a_t(p)`, sum over p, and integrate against the positive measure in (8). The frequency-independent bound (1) gives

```
T_r = sum_(p in I_X) 1/(p-1) sum_(m<=X, (m,p)=1)
        1_{P(m)>sqrt X} Phi_delta((log P(m)-log p)/L)
        + O_epsilon(X L^(-1+epsilon)).                     (9)
```

No factor depending on `1/delta` appears.

To bound the positive main term, drop coprimality. An integer m<=X has at most one prime factor q>sqrt X, and that prime is P(m). Therefore its inner sum is at most

```
2 X sum_(q prime, q>sqrt X, |log(q/p)|<=2 delta L) 1/q
   << X(delta+1/L),                                      (10)
```

uniformly for p in I_X and `delta<=1/100`. The elementary prime estimate used here and below is

```
sum_(z exp(-h)<=q<=z exp(h), q prime) 1/q
    << (h+1)/log z       (0<=h<= (log z)/2).                (11)
```

It follows directly from Chebyshev's bound and partial summation. In (10), `z=p`, `h=2 delta L` meet this condition.

Use (3) in (9). We obtain

```
T_r <<_epsilon X[delta+L^(-1+epsilon)].                     (12)
```

Every near-comparison with both largest factors greater than sqrt X and at least one in I_X is counted in `T_1+T_(-1)`. Endpoints add O(1). Thus (12) handles the narrow band where elementary cofactor sifting would lose its fixed logarithmic margin.

## 4. Small and medium largest factors

The details in this section are needed for a uniform O(delta), rather than merely deleting a fixed small-exponent population.

### 4.1 Two elementary auxiliary estimates

Put `R(n)=n/rad(n)`. For every Z>=1,

```
#{n<=X : R(n)>Z} << X/sqrt Z.                              (13)
```

Indeed `d=prod_(ell^a || n) ell^(floor(a/2))` obeys `d^2|n` and `d^2>=R(n)`. Sum `X/d^2` over `d>sqrt Z`.

For every `2<=y<=X^(1/4)`, define the multiplicative weight

```
W_y(m)=1_{P(m)<=y} rad(m)^(1/log y).
```

At prime powers it is at most e, so `W_y<=tau_3`, uniformly in y. Its Shiu prime product is

```
prod_(ell<=z) [1+(W_y(ell)-1)/ell] << log y/log z    (z>=y).
```

The product over `ell<=y` is O(1), using
`ell^(1/log y)-1 <= (e-1)log ell/log y`; the remaining Mertens product is `O(log y/log z)`. Thus, for a fixed admissible Shiu exponent,

```
sum_(m<=z, m=a mod q) W_y(m)
    << z/phi(q) (log y/log z).                             (14)
```

All constants in (14) are independent of y.

Delete `n<=X/L^4` and `R(n)>X^(1/20)`. Their count is

```
O(X/L^4+X^(39/40)).                                       (15)
```

On the retained integers, Rankin applied to `W_y`, followed by (14) with q=1, gives

```
Psi(X,y) << X/L^4+X^(39/40)
             + X (log y/L) exp(-L/(2 log y))
                 (2<=y<=X^(1/4)).                         (16)
```

For (16), `rad(n)>=X^(19/20)/L^4`, so `W_y(n)>=exp(L/(2 log y))` for sufficiently large X. This proves the stated uniformity without any uniform Dickman error estimate.

### 4.2 A largest factor p<=X^(1/4)

It suffices to count both choices of which neighboring integer has the small largest factor. Call that integer n and the other one `n+/-1`. Let `p=P(n)`, and let q be the neighboring largest factor. They are distinct primes, apart from O(1) initial cases.

Write `h=delta L`. If `p<=X^(2 delta)`, (16) bounds this population by

```
O(delta X+X/L^4+X^(39/40)).                                (17)
```

If `X^(2 delta)<2` the relevant prime range is empty. Otherwise the exponential factor in (16) is `exp(-1/(4 delta))<=1`.

Now suppose `X^(2 delta)<p<=X^(1/4)`, retaining (15)'s complement. Write `n=p m`. Necessarily

```
P(m)<=p,  m=+/-p^(-1) mod q,
rad(m)>=X^(19/20)/(p L^4).
```

Here `q!=p`, and the progression is reduced. Since p<=X^(1/4),

```
W_p(m)>=exp(L/(2 log p)).
```

Apply (14) at `z=X/p`, modulus q. Shiu's size hypothesis has a fixed margin because
`q<=p X^delta<=X^.26` whereas `z>=X^.75`. The contribution for a given p,q is at most

```
C X exp(-L/(2 log p)) log p / [p q L].                     (18)
```

We used `q-1>=q/2`. Put `t_p=log p/L`. In this range `h<(log p)/2`, so (11) and (18) give a total at most

```
C X(delta+1/L) sum_(p<=X^(1/4)) exp(-1/(2 t_p))/p
    << X(delta+1/L).                                      (19)
```

The last prime sum is bounded absolutely, uniformly in X: split `t_p` into `(2^(-j-3),2^(-j-2)]`. Each has bounded reciprocal-prime mass by (11), whereas its weight is at most `exp(-2^(j+1))`. The final interval meeting the prime 2 also has bounded mass.

### 4.3 Both factors at most sqrt X, or straddling sqrt X

If `X^(1/4)<p,q<=sqrt X`, the CRT gives at most

```
X/(pq)+1 <= 2X/(pq)
```

indices for each p,q. Summing over `|log(p/q)|<=delta L` and using (11) proves an `O(X(delta+1/L))` bound.

If `p<=sqrt X<q` and the factors are close, then

```
sqrt X<q<=X^(1/2+delta).
```

Counting multiples of q, in either neighboring coordinate, bounds the population by

```
2X sum_(sqrt X<q<=X^(1/2+delta)) 1/q
     << X(delta+1/L),                                     (20)
```

again by (11). These arguments cover all comparisons having at least one factor at most sqrt X.

## 5. Both largest factors above X^.51

Now p=P(n), q=P(n+1) are both greater than `X^beta`, with `beta=51/100`. Write

```
n=a p, n+1=b q;  bq-ap=1.
```

Then

```
(a,b)=1,  a,b<=M=X^(1-beta),
(1/2)exp(-h)<=a/b<=exp(h),  h=delta L.                     (21)
```

For fixed coprime a,b, choose `0<=c<b`, `d=(ac+1)/b`, so that

```
p=bt+c, q=at+d,  bd-ac=1,  0<=t<=T=X/(ab).
```

The two-dimensional upper sieve gives

```
# {such t : p,q prime and >X^beta}
   << T/(log T)^2 * ab/phi(ab)
    = X/[phi(a)phi(b)(log(X/(ab)))^2].                     (22)
```

Here is the uniformity audit of (22). For a prime ell not dividing ab, the two forms have two distinct roots modulo ell because their determinant is 1. For ell dividing ab there is one root. At ell=2 either the system is inadmissible (and has no counted solutions), or the usual single root occurs. Sift to `z=T^(1/10)`; both counted primes exceed z. The local product is `O((ab/phi(ab))/(log z)^2)`, and the Selberg remainder is `O(T^(1/2))`, say, absorbed in the displayed upper bound. These statements are uniform in the coefficients. In this application

```
log(X/(ab)) >= (2 beta-1)L = L/50,                         (23)
```

so `T>=X^(1/50)` and the sieve always has a fixed positive power of X available. No prime-pair asymptotic is being asserted.

Finally,

```
sum_(a<=M) 1/phi(a) << L,
sum_(a exp(-h)/2 <= b <= 2a exp(h)) 1/phi(b) << h+1,        (24)
```

uniformly in a,h. The familiar uniform estimate behind (24) follows directly from

```
1/phi(n) = (1/n) sum_(d|n) mu(d)^2/phi(d),
sum_d mu(d)^2/[d phi(d)] < infinity.
```

In an interval of ratio B/A, the inner harmonic sum after this substitution is at most `1+log(B/A)`; if its lower endpoint is below 1, use the endpoint 1. For the particular interval in (24), this still gives `O(h+1)`.

Equations (21)--(24) bound this population by

```
O_beta( X(h+1)/L ) = O_beta( X(delta+1/L) ).                (25)
```

Together (12), (15)--(20), and (25) prove Theorem A. For delta=0 there are no ties, so (A) is immediate. To obtain (A1), take `delta=(log R)/log X`, which is permitted for all sufficiently large X.

## 6. Proof of the signed-sector estimate

Return to arbitrary fixed `1/2<beta<17/33`. Because a prime p>sqrt X dividing an integer at most X is automatically its largest prime factor, the sum in (B) is

```
sum_(p in I_X) [sum_(m<=X, m=1 mod p) 1_{P(m)>p}
                -sum_(m<=X, m=-1 mod p) 1_{P(m)>p}] + O(1). (26)
```

The endpoint discrepancy is supported on primes in I_X dividing X+1, hence is at most 2. The spurious m=1 in the plus progression contributes zero.

Use the smoothed step

```
H_tau(v)=1/2+(1/pi)arctan(v/tau),   0<tau<1/100.
```

For v!=0,

```
|1_{v>0}-H_tau(v)| <= C min(1,tau/|v|),                    (27)
arctan(v/tau)=integral_0^infinity exp(-tau t) sin(tv) dt/t. (28)
```

Replace the indicator in (26) by `H_tau((log P(m)-log p)/L)`. By Theorem A and a dyadic decomposition of (27), the total error in the two progression sums is

```
O_epsilon( X[tau log(2/tau)+L^(-1+epsilon)] ).              (29)
```

For strips wider than 1/100, the trivial count O(X) suffices; their contribution is O(X tau). These progression incidences are actual neighboring comparisons, with at most the O(1) endpoints from (26), so no divisor-multiplicity factor is hidden in (29).

In the smoothed expression, the coprime main terms of residues +1 and -1 cancel identically. Lemma 1 applies to the sine/cosine separation in (28). For t>=1 the discrepancy is `O(X L^(-1+epsilon))`. For 0<t<1 it is `O(t X L^(-1+epsilon))`: write

```
sin(t(u-v))=sin(tu)cos(tv)-cos(tu)sin(tv),
```

where `0<=u,v<=1`, and use `|sin(tu)|,|sin(tv)|<=t` in Lemma 1 and its linear scaling. Thus (28) gives a total discrepancy

```
O_epsilon( X L^(-1+epsilon) log(2/tau) ).                  (30)
```

Take `tau=L^(-2)` and apply (29)--(30) first with, for example, epsilon/2. Absorbing log L proves (B).

## 7. What remains for the actual conjecture

Let `J(X)=sum_(1<=n<X)s(n)`. Absence of ties gives exactly

```
#{1<=n<X:P(n+1)>P(n)} = (X-1+J(X))/2.
```

Theorems A and B remove neither of the two remaining signed populations

```
min(P(n),P(n+1)) <= sqrt X,
min(P(n),P(n+1)) > X^beta.
```

In particular, upper bounds such as (22) cannot be subtracted as if they were asymptotics for the two orientations. For disjoint fixed exponent intervals

```
1/2<a<b<c<d<1,   b>=17/33,
```

the signed count with `(P(n),P(n+1))` in the first/second prime blocks minus its transpose is still not estimated by o(X) here. The frequency-uniform argument only changes the **test-function/cutoff** dependence; it does not increase the available modulus exponent in (6). That is the precise analytic gap of this attempt. No claim that the gap is insurmountable is made.

No proof of natural existence, no disproof, and no Lean proof of `erdos_371` has been obtained.

## Verification record

`FourierComparabilityVerification.py` checks exact finite arithmetic identities used above, including the extraction identity, the radical/square-divisor inequality, prime-factor uniqueness above sqrt X, the CRT and cofactor parametrizations, local two-linear-form root counts, and the endpoint in (26). It also checks the Fourier transform and the arctangent integral numerically. Numerical checks are not substitutes for the analytic inputs or proofs of asymptotic statements.

The initial SHA-256 of `Spec.lean` was

```
d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb
```

The verification run passed 99,999 radical/divisor checks, 99,999 exact cofactor parametrizations, 21,658 local root counts, 30,000 first-cell convolution checks, 915 signed-sector endpoint checks, 936 CRT prefix checks, and 42 finite positive-Fourier tensor checks. The 12 numerical tent-transform tests and 6 arctangent tests passed as well. At `X=1719`, the relevant central prime is 43 and the endpoint correction in (26) is **1**, so it was not silently dropped. The full output is in `FourierComparabilityVerification.log`; `Spec.lean` retained the displayed hash after the run.
