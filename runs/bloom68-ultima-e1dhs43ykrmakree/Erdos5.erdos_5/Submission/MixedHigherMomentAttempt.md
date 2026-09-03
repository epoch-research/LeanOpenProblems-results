# Mixed higher moments for the two-island prime-gap construction

## Status and scope

**No proof or disproof of Erdős #5 was obtained.** In particular, the mixed estimate (MC3) below is **not proved**. This report gives an exact finite sufficient criterion, derives its actual sieve-weight normalization, and identifies the joint estimates that are absent from the checked primary sources. No Lean file or import was changed.

The new calculations are:

1. An exact cubic two-island certificate, including its finite-parameter `K,L` threshold. The limiting triple multiplier really is **4**, in the integral normalization defined below.
2. Two explicit arithmetic mixed replacements for the triple moment: a two-prime/one-Chen combination, and a nine-term one-prime/two-Chen combination. All terms use the **same translate and the actual frozen Maynard weights**.
3. A direct joint divisor expansion showing the **product** modulus budget for the latter combination. At Merikoski's published exponents, its required `D × R` lower-bound saving disappears: the vector lower sieve has no positive coefficient.
4. Exact normalization checks: a directly justified three-prime Selberg multiplier `32 + O(delta)`, a directly justified two-rough-coordinate multiplier `64 + O(delta)`, and the Heath-Brown–Li mixed Selberg kernel value `34.7227967662...` at these exponents. The last value is a kernel comparison, **not an assertion that their unweighted fixed-shift theorem transfers automatically to the CRT weights**.

`Submission/Spec.lean` had, and retains, SHA-256

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

The report does not assume a factor `1.65` for ordinary prime pairs, does not insert an arbitrary mask into BV, and does not assume that independently bounded marginals factor.

## 1. The actual weights and the normalization

Throughout, `K` is fixed before `N -> infinity`. Use the admissibility, smooth-difference, exceptional-prime and CRT hypotheses in Merikoski, `/corpus/src/1811.03008/limitp2.tex`, lines **353–390**. Write

- `R_N = {N < n <= 2N : n = b mod W}`;
- `Z_exc = Z_(N^(4 epsilon))`;
- `B = (phi(W)/W) log N`;
- `A_N = N/(W B^K)`;
- `X_i(n) = 1_P(n+h_i)`.

The primitive functions in that source give

```
lambda_d = (product_i mu(d_i)) sum_a product_i f_(i,a)(log d_i/log N),
F(t) = sum_a product_i f'_(i,a)(t_i),
omega_F(n) = (sum_(d_i | n+h_i) lambda_d)^2.
```

The exceptional-prime coprimality restriction on `lambda` is retained. Each tensor summand has total support at most a small `delta`, so `product d_i <= N^delta`.

For a subset `S` of coordinates define

```
J_S(F) = integral_(t outside S) |integral_(t in S) F(t) dt_S|^2 dt_(outside S),
I(F) = J_empty(F).
```

For symmetric `F`, write `J_r` for any `J_S` with `|S|=r`. Thus `J_1` is BFM's `J_K`, `J_2` is its `L_K`, and **the triple integral is `J_3`, with three integrations INSIDE the square**. No factor `3!`, `2`, or power of `log N` is hidden in this definition.

The mass and first-prime evaluations are

```
sum_R_N omega_F = (1+o(1)) A_N I,
sum_R_N X_i omega_F = (1+o(1)) A_N J_{i}.
```

Source: BFM, `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`, **1180–1238, 1280–1337**. Its displayed triple-free lemma has labels whose numbering differs from later citations; the line references here identify the actual statements.

For any `S`, define the **frozen weight**

```
nu_S(n) = (sum_(d_i | n+h_i, d_i=1 for i in S) lambda_d)^2
          * 1_(gcd(product_(i in S)(n+h_i), Z_exc)=1).
```

On the event that every coordinate of `S` is prime, `nu_S = omega_F`: all those divisors must equal 1. This is the actual freezing operation at Merikoski **394–399**, extended by exactly the same identity to more coordinates.

Freezing `r` coordinates leaves a quadratic form with `K-r` divisor coordinates and squared norm `J_S`. Accordingly, before imposing any primes its mass scale is

```
A_N B^r J_S.
```

Keeping **one** frozen coordinate prime reduces that to

```
X_base := sum_R_N X_i nu_S = (1+o(1)) A_N B^(r-1) J_S,  i in S.       (1)
```

This follows by expanding the square and using the one-prime BV theorem, not by assuming a joint prime asymptotic. Merikoski **471–476** gives precisely the `r=2` computation. The analogous `r=3` computation has `K-3` unfrozen divisor coordinates and scale `A_N B^2 J_S`.

In particular, a proposed triple bound must be compared with

```
sum_R_N X_i X_j X_k omega_F <= (a_3+o(1)) A_N J_{ijk}.               (2)
```

It must not be compared with `A_N B J_{ijk}`, or with a product of three independent first moments.

## 2. Exact finite polynomial certificate

Partition the coordinates into the two prescribed islands `H_L,H_R`, each of size `q=K/2`. Put

```
x(n) = sum_(i in H_L) X_i(n),
y(n) = sum_(i in H_R) X_i(n).
```

Fix an integer `L>=2`, with `q>=L+1`, and set

```
mu = 1/binom(L,2),
h_L = 2(L+1)/3,
p_L(v) = v - mu binom(v,3).
```

This is an exact finite calculation, not a continuous relaxation:

```
p_L(v+1)-p_L(v) = 1 - binom(v,2)/binom(L,2).
```

Hence the maximum on the nonnegative integers is attained at `L,L+1`, and equals `h_L`. Therefore

```
Q_L(x,y) = x+y-h_L-mu[binom(x,3)+binom(y,3)] <= 0
```

whenever `x=0` or `y=0`. Consequently

```
sum_R_N omega_F Q_L(x,y) > 0                                    (3)
```

forces a translate containing a prime in **both** islands.

Let `T_3` be the actual within-island triple sum, with unordered triples:

```
T_3 = sum_(S subset H_L or S subset H_R, |S|=3)
          sum_R_N omega_F product_(i in S) X_i.
```

The exact finite sufficient condition is

```
T_3 < binom(L,2) [sum_R_N omega_F(x+y) - h_L sum_R_N omega_F].      (4)
```

In terms of the known mass/first-moment integrals, any upper estimate

```
T_3 <= (a_3+o(1)) A_N 2 binom(q,3) J_3
```

therefore suffices if

```
K J_1 - [2(L+1)/3] I - [a_3/binom(L,2)] 2 binom(K/2,3) J_3 > 0.  (FC3)
```

This is the promised exact finite polynomial/integral criterion. For a nonsymmetric function, replace `K J_1` by `sum_i J_i` and the last integral by the sum of the individual within-island `J_S`.

### Why the limiting threshold is 4, not 8 or 2

The requisite fixed-order integral ratios can be derived from the actual BFM product test, rather than postulated as a higher-moment theorem. Put

```
a = log K - 2 log log K,
T = (exp(a)-1)/a,
g(u) = 1/(1+a u) for 0<=u<=T, and 0 otherwise,
f_sigma(t) = product_i g(K t_i/sigma) * 1_(sum_i t_i<=sigma).
```

This is the test in BFM **1661–1686**, scaled into a small simplex. Set

```
c_2 = integral g^2 = (1-exp(-a))/a;     integral g = 1.
```

For a random variable `V` with density `g^2/c_2`, direct integration gives

```
E V = [a-1+exp(-a)]/[a(1-exp(-a))],
E V^2 = [exp(a)-2a-exp(-a)]/[a^2(1-exp(-a))].
```

Thus `E V=1-1/a+o(1/a)` and
`Var(sum_(1..K) V_i) = O(K^2/(a^2 log^2 K))`. Chebyshev shows that deleting the portion of the product cube outside `sum u_i<=K` changes its squared norm by a relative `O(log^(-2) K)`.

For each fixed `r`, the inner `r`-coordinate integral is bounded above by the full cube integral. It equals that full cube integral whenever the sum of the other coordinates is at most `K-rT`. The same Chebyshev argument applies, since the remaining mean is below `K-rT` by `(1+o(1))K/a`. Hence

```
J_r(f_sigma)/I(f_sigma)
  = (1+O_r(log^(-2) K)) [sigma/(K c_2)]^r.                       (5)
```

Choose `sigma=(L+1)c_2`, so eventually `sigma<delta`. Then
`K J_1/I=L+1+o_K(1)` and `J_3/I=((L+1)/K)^3(1+o_K(1))`.
For each sufficiently large **fixed** `K`, smoothing and finite tensor approximation preserve these strict inequalities. One can use nonnegative smooth rectangular approximations and their tail primitives, so this is a test of the actual divisor-weight form, not an assumed extra class of weights. No growing-order uniformity is used.

Ignoring only those controllably small approximation errors, (FC3) is

```
a_3 < 4 L(L-1) / [(L+1)^2 (1-2/K)(1-4/K)].                      (6)
```

For `K -> infinity` and then large `L`, the right side approaches **4 from below**. Thus a uniform estimate with any fixed `a_3<4` would indeed close the two-island construction. This calculation does **not** prove that estimate.

There is an exact normalization sanity check: at `K=2(L+1)` the right side of (6) is 4; for larger `K` it is smaller. The active-one-island Bernoulli model has within-island `r`-point factors `2^(r-1)` and zero cross-island occupancy, so its triple factor is exactly 4. The calculation is consistent with, not a way around, that obstruction.

More generally, for any finite polynomial

```
Q(x,y)=sum_(r,s) c_(r,s) binom(x,r)binom(y,s),
```

the exact axis conditions are the finitely many inequalities
`Q(v,0)<=0` and `Q(0,v)<=0`, `0<=v<=q`. The expectation is the same linear combination of **joint weighted factorial moments**. A lower bound uses lower moment estimates for positive coefficients and upper estimates for negative coefficients. Merely having upper bounds for cross-island moments does not supply a positive expectation. This is a finite linear feasibility criterion once the directional moment bounds are specified.

## 3. A genuinely mixed arithmetic target

We now make the additional arithmetic information explicit. Fix

```
Y=N^alpha, Z=N^beta, 0<alpha<beta<1/4,
```

with the published choice `alpha=1/7`, `beta=3/14` available. For a coordinate `i` write

```
R_i = 1_(gcd(n+h_i, P(Y))=1),
k_i = number of distinct primes p in (Y,Z] dividing n+h_i,
D_i = R_i k_i,
T_i = R_i max(k_i-2,0),
U_i = R_i - D_i/2 + T_i/2.                                     (7)
```

These are actual arithmetic functions of `n+h_i`. Exactly,

- `U_i=1` if `R_i=1,k_i=0`;
- `U_i=1/2` if `R_i=1,k_i=1`;
- `U_i=0` otherwise.

In particular, `0<=X_i<=U_i<=1`.

### Relation to the precise Chen switching term

Merikoski **402–415** uses, instead of `T_i`,

```
T_i^sw = sum_(Y<p<q<r<=Z) sum_(gcd(s,P(q))=1) 1_(n+h_i=pqrs).
```

On integers with no squared prime factor from `(Y,Z]`, this is exactly `R_i max(k_i-2,0)`: `p,q` must be the two smallest interval prime divisors, and there are `k_i-2` choices of `r`.

For an **exact** pointwise polynomial it is safer to use (7). The two versions differ only on the exceptional square-divisibility rows, by `O_alpha(1)`. Their total contribution to any of the fixed-order mixed sums below is negligible, directly: the weights are `N^o(1)` for fixed `K`, the other pattern counts are bounded in terms of `alpha`, and

```
# {n in R_N : p^2 | n+h_i for some Y<p<=Z}
  << N/(W Y) + N^beta.
```

Here `p` is coprime to `W` for large `N`. Taking `epsilon` small gives
`N^o(1)[N/(WY)+N^beta]=o(A_N)`. This handles repeated factors without relying on an unqualified pointwise switching identity for nonsquarefree integers, and without any masked BV assertion.

### The less wasteful mixed target: two exact primes and one Chen pattern

Let `mathcal S` be the set of unordered triples wholly in one of the two islands. Define

```
M_2P = (1/3) sum_(S in mathcal S) sum_(i in S)
          sum_R_N nu_S [product_(j in S minus {i}) X_j] U_i.       (8)
```

Every summand is nonnegative. Freezing and `X_i<=U_i` prove **exactly** that

```
T_3 <= M_2P.
```

Thus the following is a precise sufficient mixed estimate:

```
M_2P <= (4-eta+o(1)) A_N sum_(S in mathcal S) J_S(F),  eta>0.     (MC3)
```

It need only hold for the chosen tests and CRT tuples, not for all conceivable masks. An even weaker finite target is to bound (8) by the right side of (4), with a fixed positive asymptotic margin.

**(MC3) is the first unproved arithmetic inequality in this attempted closing argument.** It is a signed combination of the same-translate quantities

```
<nu_S X_j X_k R_i>,   <nu_S X_j X_k D_i>,   <nu_S X_j X_k T_i>,
```

with coefficients `1,-1/2,+1/2`. It is neither an unweighted marginal statement nor a polarization of the ordinary one-prime forms.

### Eliminating one of the two exact primes produces nine genuinely mixed terms

A more generous majorant, using only one exact prime at a time, is

```
M_1P = (1/3) sum_(S in mathcal S) sum_(i in S)
          <nu_S X_i U_j U_k>,          {j,k}=S minus {i}.
```

Again `T_3<=M_1P`. For a fixed oriented triple, set

```
C_ab = <nu_S X_i A_a(j) A_b(k)> / (A_N J_S),
(A_0,A_1,A_2)=(R,D,T).
```

The exact coefficient for its majorant is

```
C_00 - (C_10+C_01)/2 + (C_20+C_02)/2
     + C_11/4 - (C_12+C_21)/4 + C_22/4.                         (9)
```

For directional estimates, the `C_00,C_20,C_02,C_11,C_22` entries must be bounded **above**, whereas `C_10,C_01,C_12,C_21` must be bounded **below**. An upper bound below 4 for the appropriate `J_S`-weighted average of (9) would suffice by (FC3). No entry in (9) is replaced by a product of one-coordinate marginal estimates.

This exhibits exactly where a genuinely mixed improvement could enter. The published one-coordinate Chen inequality by itself gives none of the necessary joint lower estimates.

## 4. What the actual divisor expansion does give, and where it stops

### 4.1 The joint modulus is a PRODUCT, not two separate BV budgets

Consider `<X_i nu_S 1_(u|n+h_j) 1_(v|n+h_k)>` for `S={i,j,k}`. Expand the frozen square and put

```
q_l = [d_l,d'_l],   Q=product_(l outside S) q_l <= N^(2 delta).
```

For compatible nonzero terms, `W,u,v,q_l` are pairwise coprime, excluding `Z_exc`. The smooth-difference hypothesis is exactly what enforces this. The inner sum is a **single prime count** in one reduced residue class modulo

```
W u v Q.                                                        (10)
```

Its main term is the prime interval count divided by
`phi(W) phi(u) phi(v) product_l phi(q_l)`; its error is a usual prime-AP error at (10). Crucially, the coprimality restrictions remain in the coefficient sum. We do **not** silently replace the exact coefficient-dependent main term for each `u,v` by a factorized marginal.

BV controls the aggregate AP errors, with the usual fixed divisor-multiplicity factors, for

```
u v <= N^(1/2-4 delta),  epsilon sufficiently small relative to delta. (11)
```

This follows by the same Cauchy–Schwarz/divisor-multiplicity grouping displayed at Merikoski **489–517**, now with the additional two divisor labels. The original BV theorem is at **223–225**. This is a legitimate joint *divisor* expansion. It is not distribution of primes after an arbitrary arithmetic mask.

After the usual coprimality/Euler-factor evaluation, the leading sieve density for the two remaining forbidden residues is `2/(p-1)` at primes outside `W Z_exc`; for one coordinate it is `1/(p-1)`. Each rough coordinate contributes the Mertens scale `e^(-gamma)/(alpha B)`. The total level in (11) must be shared by both coordinates.

### 4.2 A completely direct mixed upper bound: 64, not 4

There is a straightforward bound that avoids transferring any unweighted mixed-sieve theorem. Choose `sigma=1/4-2 delta`, and a smooth function `G` supported below `sigma/2`, with `G(0)=1`, approaching the optimal linear cutoff. Since `sigma/2<alpha=1/7`, on a `Y`-rough coordinate

```
sum_(e|n+h_j, gcd(e,Z_exc)=1) mu(e)G(log e/log N) = 1.
```

The square therefore majorizes `R_j`. Use a separate such factor for `R_k`, multiply by `X_i nu_S`, and expand all squares. The combined total divisor support is at most `delta+sigma`; its squared modulus is below the one-prime BV limit. The BFM quadratic-form calculation gives

```
<X_i nu_S R_j R_k>
 <= [ (integral |G'|^2)^2 + o(1)] A_N J_S
 <= [64+O(delta)+o(1)] A_N J_S.                                 (12)
```

This is a genuine same-translate, weighted mixed calculation, but its constant is far too large.

### 4.3 Inspecting the stronger mixed Selberg kernel

Heath-Brown–Li, `/corpus/src/1504.00533/1504.00533.tex`, **474–534**, give a mixed-dimension Selberg calculation. Its kernel is

```
B_HBL(s_1,s_2)^(-1)
 = exp(-2 gamma) integral_(w_1/s_1+w_2/s_2<=1) rho(w_1)rho(w_2) dw_1 dw_2,
```

where `rho` is Dickman's function. Importantly, **their**

```
s_i = log(D)/(2 log z_i),
```

not `log(D)/log z_i`; the source explicitly warns about this at **531–534**.

At `D=N^(1/2-o(1))`, `z_1=z_2=Y=N^(1/7)`, the limiting parameters are `s_1=s_2=7/4`. The equal-threshold kernel is the limit of their mixed-dimension formula. In the normalization of (1), with two Mertens factors included, its coefficient is

```
kappa_RR = 1/[alpha^2 H(7/4)],
H(s)= integral_(u+v<=s) rho(u)rho(v) du dv.
```

For `1<=s<=2`, at most one coordinate exceeds 1, so `rho(u)=1-log u` there gives the exact elementary evaluation

```
H(s)=s^2/2 - 2 integral_1^s (s-u)log u du
    =2s^2-s^2 log s-2s+1/2.
```

Consequently

```
H(7/4) = 1.411176649447768023295403967...,
kappa_RR = 49/H(7/4) = 34.72279676621281871048366607....          (13)
```

This is a **source-kernel and normalization comparison**, not an unexplained assertion of uniform transfer of HBL's theorem to growing CRT tuples and arbitrary Maynard weights. Such an adaptation would have to retain the exact coefficient expansion in §4.1 and evaluate the resulting main form. Even granting that adaptation at this coefficient, it would only reduce the leading entry of (9) from 64 to about 34.72, not to a value below 4. No claimed proof in this report depends on that adaptation.

### 4.4 The needed negative `D × R` saving is unavailable at the published exponents

For `C_10`, first expose the prime divisor `p=N^t`, `alpha<t<=beta`, at coordinate `j`. Both `j` and `k` must still be `Y`-rough. The remaining product level is at most

```
N^(1/2-t-O(delta)).
```

For a two-coordinate vector sieve using linear parameters `s_1,s_2`, this forces

```
alpha(s_1+s_2) <= 1/2-t-O(delta).                               (14)
```

HBL's actual lower kernel is

```
f_lin(s_1)F_lin(s_2)+F_lin(s_1)f_lin(s_2)-F_lin(s_1)F_lin(s_2),  (15)
```

optimized subject to the **shared** level constraint. See HBL **284–298, 401–438**. Merikoski **421–435** states `f_lin(s)=0` for `s<=2`.

With `alpha=1/7`, `t>=1/7`, (14) gives

```
s_1+s_2 <= 5/2-O(delta).
```

If `s_1,s_2>=1`, both are at most `3/2`, so both lower-sieve functions vanish. The expression (15) is negative; after taking the trivial nonnegative lower bound, the available saving is **zero**. Equivalently, HBL's optimization restricted to `s_i>=2` has no feasible pair. This is why Merikoski's positive one-coordinate `S_2` saving cannot simply be repeated while also imposing roughness at the other coordinate.

The negative `D × T` terms are not supplied either. Before switching, their four exposed interval primes already have product at least `N^(4/7)`, above the half-level budget. Merikoski's switching argument supplies an **upper** bound for its one-coordinate `S_3`, not the **lower** bound for `D × T` required in (9). Products of two switched patterns are not the single multiplicative convolution in its BV proposition.

This is a failure of this specific source-based mixed estimate, not a theorem that every possible mixed higher-order method must fail.

### 4.5 Keeping two primes exact does not license a masked BV invocation

For the less wasteful target (MC3), expanding the divisors instead leaves inner sums

```
sum_(N<n<=2N, n=a mod M) X_j(n) X_k(n),                         (16)
```

possibly with a third-coordinate divisor exposed. Neither Merikoski's prime BV theorem nor its almost-prime BV theorem estimates (16) with the lower-bound strength needed for the negative Chen term. In particular:

- Its prime BV theorem concerns a **single** `Lambda` in residue classes.
- Its almost-prime theorem, **246–255**, concerns a **multiplicative convolution** `f*g` at one integer, with a prime factor and a rough bounded cofactor weight.
- `X_j(n)X_k(n)` is an **additive shifted correlation**, not such a convolution.
- The existing weighted pair **upper** form does not provide a lower or equidistribution estimate for (16), nor is it an upper theorem after inserting `R_i,D_i,T_i` at no cost.

An estimate specifically for the signed aggregate (MC3) could be weaker than a full pair-distribution theorem. It would nevertheless be new arithmetic information. It has not been derived here.

## 5. Honest three-prime baseline from the weights

For completeness, the elementary unconditional triple baseline in (2) is **32**, not 4.

Freeze `S={i,j,k}`. Let `G(u,v)` be smooth, supported on `u,v>=0`, `u+v<=sigma`, with `G(0,0)=1`, where `sigma=1/4-2 delta`. On simultaneous primes at `j,k`, the two-coordinate divisor sum with coefficients

```
mu(e)mu(f)G(log e/log N, log f/log N)
```

equals 1. Its square, multiplied by `X_i nu_S`, majorizes the triple indicator times the original weight. Expand all squares. The modulus support is at most `N^(2(delta+sigma))W`, so the same single-prime BV argument as BFM **1506–1616** applies. The main term is

```
A_N J_S integral_(u,v>=0) |partial_u partial_v G|^2 du dv.
```

Since `integral G_uv = G(0,0)=1`, Cauchy–Schwarz on the triangle of area `sigma^2/2` gives

```
integral |G_uv|^2 >= 2/sigma^2.
```

The infimum is approached by smoothing

```
G(u,v)=(1-(u+v)/sigma)_+^2,
```

whose mixed derivative is `2/sigma^2` inside the triangle. Therefore

```
sum_R_N X_iX_jX_k omega_F
 <= (32+O(delta)+o(1)) A_N J_S.                                 (17)
```

This is the optimal cost **within this auxiliary-square construction**, not a claim of an optimal unconditional prime-triple theorem. It lies well above the required 4. Merikoski's small-support pair improvement cannot be iterated as a free scalar factor: the third-coordinate majorant changes the support and the mixed distribution problem.

## 6. What the checked primary sources actually improve

### Merikoski: one prime / one Chen decomposition

`/corpus/src/1811.03008/limitp2.tex`:

- **353–390**: the weights, support, CRT hypotheses, and `3.99+O(delta)` weighted pair upper bound.
- **402–415**: the one-coordinate Chen decomposition.
- **529–556**: the positive lower bound for its single `S_2`, using remaining level `N^(1/2-4 delta)/p`.
- **579–614**: switching for the single `S_3`; one remaining prime is majorized and one almost-prime sequence is distributed.
- **656–677**: the actual coefficient `Omega_1-Omega_2+Omega_3`, with
  `Omega_1<=4.19`, `Omega_2>=0.279`, `Omega_3<=0.076`; hence `<=3.987<3.99` before the small-support error. Direct quadrature checks give `Omega_1=4.1864411748...`, `Omega_2=0.2796617622...`. No triple constant is asserted there.
- **736–775**: the quadratic occupancy polynomial, not a mixed third-moment estimate.
- **188–189**: the author explicitly identifies a pair multiplier below 2 as sufficient for the full conjecture, and discusses the parity obstruction.

The three terms of Chen's formula are **not three prime coordinates**. Treating `S_3` as a prime-triple estimate is a category error: its `p,q,r` are factors of one shifted integer.

### Heath-Brown–Li: genuinely mixed, but almost-prime conclusions

`/corpus/src/1504.00533/1504.00533.tex`:

- **65–76**: the theorem counts `p` prime, `p+2` with at most two prime factors, and `p+6` with at most **76** prime factors, with lower bound `>>x/log^3 x`.
- **284–298, 409–438**: the vector-sieve product and lower kernels with a shared product level.
- **474–534**: the mixed-dimension Selberg kernel used for the calculation (13).
- **542–556**: BV for **products** of primes in residue classes, not for shifted joint primality.
- **990–1001**: its final roughness exponents are very unequal (`1/11` and `1/410`), consistent with retaining an almost-prime third coordinate, not making it prime.

Thus there is real mixed information in this source, but neither its conclusion nor its displayed kernels give (MC3) or a weighted triple coefficient below 4 on the required CRT support.

### Lichtman: `3.29956` times the FULL Hardy–Littlewood main term

`/corpus/src/2109.02851/lineartwin8.tex`, **84–94**, explicitly defines

```
Pi(x)= [2x/log^2 x] product_(p>2) (1-2/p)/(1-1/p)^2,
```

and states

```
pi_2(x) <= (3.29956+o(1)) Pi(x).
```

The leading 2 is already in `Pi(x)`. The multiplier is **3.29956**, not `1.64978`, relative to full HL. It is still greater than 2 even before confronting transfer issues.

The strengthened distribution statements use specified (programmably) factorable **modulus coefficients** and fixed residues: **62–76, 149–169, 208–225**. “Triply well-factorable” describes a factorization of a modulus-coefficient sequence, not a prime-triple correlation. The products-of-primes extension at **1102–1116** is likewise multiplicative. The paper itself contrasts fixed-residue twin-prime applications with growing-residue problems at **1151**. None of these statements permits arbitrary CRT/Maynard/pattern masks to be inserted into the prime variable.

## 7. What would close the argument, and what remains

For any fixed `C>0`, the existing Erdős–Rankin construction can place the survivors in two groups of diameter `o(log N)`, separated by `(C+o(1))log N`, with the intervening integers composite on the CRT rows. Merikoski's covering statement is at **778–798**. The missing issue remains simultaneous occupancy of these two prescribed groups.

A uniform proof of **(MC3)** for the tests from §2 and these tuples would, via the exact finite criterion (FC3), force both groups to contain primes. The last prime in the left group and first prime in the right group would then be **globally consecutive**. Their gap would be `(C+o(1))log N`. PNT gives `log(index)=log N+o(log N)` for such primes, so this would also give the normalization in the untouched specification. The limit `C=0` is already supplied by known small-gap results.

But **(MC3) has not been proved**. The first concrete source-based attempt to estimate it encounters the shifted two-prime sums (16). Replacing the second prime by a Chen majorant yields the explicit nine-term criterion (9), where the needed joint lower savings are not supplied; at the published exponents the `D × R` vector-sieve saving is exactly zero after the trivial lower bound. No closing inference is drawn from the pure upper hierarchy or from marginal pattern counts.

### Verification

`Submission/check_mixed_higher_moment.py` checks:

- exact rational cubic maxima and the finite threshold algebra;
- the nine-term signs and the exact nonnegative Chen majorant;
- compatibility of the threshold with the active-one-island binomial model;
- the elementary auxiliary-simplex normalization and product-test moment formulas;
- the closed-form Dickman integral and its numerical value, independently by quadrature;
- the specification hash.

These checks verify the finite algebra and constants, **not** the unproved analytic estimate (MC3). No source theorem is claimed to have been formalized in Lean, and no conjecture declaration was used as an assumption.
