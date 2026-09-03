# Joint EXACT factor patterns: substantive attempt and precise stopping point

## Status

**No proof or disproof of Erdős #5 was obtained.** In particular, no simultaneous prime occupancy of the two prescribed CRT endpoint groups was proved. The original `Submission/Spec.lean` was not edited or used as a premise. Its SHA-256 remains

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

This investigation has three concrete outputs, none presented as a solution of the prime-gap problem:

1. A quantitative boundary calculation explaining exactly why a proved, genuinely joint theorem on the **exact numbers of large prime factors** does not count numbers with **exactly those factors and no residual cofactor**.
2. A rigorously derived, power-rough, exact-factor-pattern corollary of Fouvry–Tenenbaum's dispersion theorem, retaining its precise summation structure and error. The missing inference is visible explicitly when a factor-pattern condition is inserted on the complementary cofactor.
3. An explicit nonnegative completion showing that even ideal, fully pattern-resolved mixed **divisor moments** on both rough endpoints can coexist with a zero prime–prime cell. This is stronger information than just one-coordinate marginals. The finite algebra has been formalized independently in `JointPatternAudit.lean`; it imports only Mathlib.

All sources cited below were inspected in `/corpus/src`. The claims about the state of available estimates refer to these checked results, not to a proof that no possible arithmetic approach can work.

## 1. Setup, exact decomposition, and harmless prime-power errors

Let the physical height be `X`, with offsets `h_i = O(log X)`, so all endpoints are at most `3X` for large `X`. Write `y = X^eta`, where `eta > 0` is fixed. Let

```
E_r(m) = 1_{m squarefree, P^-(m)>y, Omega(m)=r}.
```

There are at most `floor(log(3X)/log y)` factors. Thus, on squarefree rough endpoints, `R = sum_r E_r`, and `E_1 = 1_P`. For a nonnegative weight `W(n)` incorporating the SAME row, CRT class, middle-composite condition and any sieve weight, define

```
N_rs(i,j) = sum_n W(n) E_r(n+h_i) E_s(n+h_j).
```

The generating function `Z_ij(z,t) = sum_{r,s} N_rs(i,j) z^r t^s` is an exact finite polynomial. The block quantity needed is the sum of its `(1,1)` coefficients over `i in L, j in R`. We do not evaluate those coefficients.

Removing squareful rough endpoints causes an error bounded by

```
O(K ||W||_infinity X/y),
```

because the number of integers at most `3X` divisible by some `p^2`, `p>y`, is at most `3X sum_{m>y} 1/m^2 = O(X/y)`. For fixed-dimensional standard divisor weights of size `X^{o(1)}` and a CRT modulus `Q=X^{o(1)}`, this is power-saving relative to an `X^{1-o(1)}` pair-count scale. It is not the obstruction.

Without CRT or divisor weights, the pair-count scale is already `X/log^2 X`, up to the local factor. For a squarefree CRT modulus and a fixed reduced row avoiding both endpoint roots, the Hardy–Littlewood *benchmark* is

```
B(X;Q,h) = X/(Q log^2 X)
           * product_{p|Q} (1-1/p)^(-2)
           * product_{p not dividing Q} (1-nu_p(h)/p)/(1-1/p)^2,
```

where `nu_p(h)` counts the two roots modulo `p`. This is an error-comparison benchmark, NOT an asymptotic asserted here. No global prime fraction is transferred to a conditioned row.

The efficient CRT geometry from the prior audit is not challenged: once both groups contain primes in the same row, the last left prime and first right prime are globally consecutive, their gap is `C log X+o(log X)`, and `log(index)=log X-log log X+O(1)` gives the normalization in `Spec.lean`. What remains unproved is the arithmetic occupancy event.

## 2. A genuine joint theorem: exact LARGE-factor counts

Joni Teräväinen, **On binary correlations of multiplicative functions**, arXiv:1710.01195, proves a result especially close to the proposed route. Its theorem labelled `theo_omega` says, for fixed `a,b in (0,1)`, `0<=r<1/a`, `0<=s<1/b`, that

```
log-density{omega_{>n^a}(n)=r, omega_{>n^b}(n+1)=s}
  = density{omega_{>n^a}(n)=r} * density{omega_{>n^b}(n)=s}.
```

The joint set even has positive lower asymptotic density. This is real two-coordinate exact-count information, including counts larger than 2. But it counts only the large factors; all smaller factors are unrestricted.

The one-coordinate constants appearing in the proof are

```
I_(a,r)/r!,
I_(a,r) = integral_{u_i>=a, sum u_i<=1}
          rho((1-sum u_i)/a)/(u_1 ... u_r) du_1 ... du_r.
```

The Dickman factor explicitly counts the residual smooth cofactor. These are volume integrals in `r` dimensions, not the boundary integrals for complete factorizations.

The underlying correlation theorem (`theo_bincorr`) is the following. For fixed nonzero `h`, `1<=omega(X)<=log(3X)` tending to infinity, `x>=x_0(epsilon,h,omega)`, real multiplicative `g_1,g_2` bounded by 1, and `g_1` satisfying

```
| x^(-1) sum_{x<=n<=2x, n=a mod q} g_1(n)
  - (qx)^(-1) sum_{x<=n<=2x} g_1(n) | <= epsilon/q
                  (1<=a<=q<=epsilon^(-1)),
```

one has

```
(1/log omega(x)) sum_{x/omega(x)<=n<=x} g_1(n)g_2(n+h)/n
 = mean_[x,2x](g_1) mean_[x,2x](g_2) + o_{epsilon->0}(1).
```

The functions may depend on `x`; the error is absolute, with the stated threshold on `x`. This stronger result should not be dismissed as merely raw log-Chowla. Nevertheless, its error still does not have the relative strength required on two power-rough endpoints.

### 2.1 The boundary calculation

For complete squarefree rough factorizations, PNT and summation over the first `r-1` prime factors give

```
# {X<n<=2X: E_r(n)=1} = (a_r(eta)+o(1)) X/log X,
```

where `a_1=1`, and for `r>=2`

```
a_r(eta) = 1/r! * integral_{u_i>=eta (i<r), sum_{i<r}u_i<=1-eta}
          du_1 ... du_(r-1)
          / [u_1 ... u_(r-1) (1-sum_{i<r}u_i)].
```

The factor `1/r!` accounts for ordered factorizations. In particular,

```
a_2(eta) = log((1-eta)/eta),
a_3(eta) = (1/3) integral_eta^(1-2eta)
           log((1-t-eta)/eta)/(t(1-t)) dt.
```

Here and below an empty simplex gives zero. These are single-integer asymptotics, not a hypothesis of independence at shifted arguments.

Let `m_y(n)` be the entire `y`-smooth part of `n`. Choose fixed

```
0 < delta < min(eta, 1-r eta).
```

Count numbers in `(X,2X]` having exactly `r` large prime factors and `m_y(n)<=X^delta`. Except for the already negligible repeated large factors, uniquely write

```
n = m p_1 ... p_r,  m<=X^delta<y,  p_i>y.
```

Every integer `m<=X^delta` is automatically `y`-smooth. Applying the preceding single-coordinate PNT calculation uniformly for `u=log m/log X in [0,delta]`, and summing `1/m`, gives

```
N_(r,delta)(X)
 = X integral_0^delta a_r(eta/(1-u))/(1-u) du + o_(eta,r,delta)(X).
```

For small fixed `delta`, this is

```
(a_r(eta) delta + O_(eta,r)(delta^2)) X + o_(eta,r,delta)(X).
```

By contrast, **requiring `m=1`** has size `(a_r(eta)+o(1))X/log X`. Thus a fixed exponent window for a tiny cofactor still contains about `delta log X` times the mass of the complete factorization. To force `m=1` by size requires `delta log X < log 2`: this is a shrinking window of order `1/log X`.

Neither the displayed `o_(delta)(X)` nor Teräväinen's absolute correlation error controls that shrinking window. On both coordinates the target mass is of order `X/log^2 X`. Finite polynomial interpolation of the joint large-factor generating function still yields only an absolute `o(1)`, not `o(1/log^2 X)`.

An especially transparent instance: for fixed `a>1/2`, the density of `P^+(n)>n^a` is `-log a`. Primality instead requires `P^+(n)>n/2`, corresponding to `a=1-log 2/log n`. Fixed-parameter independence cannot be evaluated at this moving boundary.

Sending `delta` to zero *after* taking a limit in `X` does not repair the problem. Complete factorizations are zero-density boundary events in that limit. No uniform relation between the thresholds `x_0(epsilon,...)` and `1/log^2 x` was proved by the source. The issue persists even for a fixed shift, before the additional uniformity in a growing CRT modulus and `h~C log X` is requested.

## 3. EXACT total factor-pattern theorems: what their constructions do

Goldston–Graham–Pintz–Yıldırım, arXiv:0803.2636, really proves, for example:

- `Omega(x)=Omega(x+1)=A` infinitely often for each integer `A>=4`;
- `Omega(x)=Omega(x+2)=B` infinitely often for each integer `B>=5`;
- both `x,x+1` have exponent pattern `{2,1,1,1}` infinitely often.

The sequel by Goldston–Graham–Panidapu–Pintz–Schettler–Yıldırım, arXiv:2003.03661, gives fixed exponent patterns for every positive shift. In particular, for even `h`, or `15` not dividing `h`, the pattern `{2,1,1,1,1}` occurs at both endpoints infinitely often. The remaining case has pattern `{3,2,1,1,1,1,1}`.

Their mechanism matters. The Basic Theorem gives two unspecified forms in an admissible triple simultaneously taking `E_2` values with their prime factors larger than any **fixed** constant. The adjoining-primes theorem constructs new forms `K_i` with relations

```
|c_ij r_i K_i - c_ji r_j K_j| = h.
```

It uses `L_i(x)=r_i mod r_i^2`, a CRT class modulo `(product_i r_i)^2`, and divides the resulting forms by `r_i`. The desired integers are `c_ij r_i K_i`, not `K_i` themselves. Their prescribed extra prime factors belong to the fixed relation coefficients.

For each such fixed construction, the resulting endpoints have a fixed prime divisor, so eventually they are absent from `P^->X^eta`. This is a direct support failure, not an unknown constant in an otherwise usable rough-pattern asymptotic. Choosing all relation coefficients anew with `X` would need quantitative height and uniformity assertions not supplied by these infinitude theorems; it also would not turn the composite endpoints into primes.

Peeling the extra factors does not preserve the required gap: from `n=A P`, `n+h=B Q` one gets `B Q-A P=h`, not `Q-P=h`. If both endpoints are power-rough and `y>|h|`, they are coprime since their gcd divides `h`. Thus no nontrivial common factor can be divided out to rescue the original difference.

## 4. A proved exact-pattern dispersion corollary

Fouvry–Tenenbaum, **Multiplicative functions in large arithmetic progressions and applications**, arXiv:2004.04766, has a class `F(D,K)` broader than the fixed-prime-periodicity class in Drappeau–Topacogullari. Its functions are multiplicative, bounded by `tau_K`, and constant on primes in each residue class modulo `D` within intervals `(Upsilon_j,Upsilon_(j+1)]`, with

```
Upsilon_(j+1)/Upsilon_j >= 1 + 1/(log(2 Upsilon_j))^K.
```

Thus a cutoff at `y=X^eta`, and finitely many fixed power-sized factor bins above it, ARE allowed. It would be incorrect to reject this theorem just because the rough cutoff moves with `X`.

Define

```
Delta_f(x;q,a) = sum_{n<=x, n=a mod q} f(n)
                 - 1/phi(q) sum_{n<=x, (n,q)=1} f(n).
```

Corollary `easy1` (with its class modulus `D=1`) says: for fixed `A,epsilon,K>0`, suitable `B,C` exist, and

```
| sum_{d<=D_0, (d,a)=1} xi_d
    sum_{q<=Q_0, (q,a)=1} Delta_f(x;dq,a) |
 <= C x/(log(3x))^A,
```

provided

```
D_0 <= x^(1/105-epsilon),
D_0 Q_0 <= x/(log(3x))^B,
|xi_d| <= tau_K(d),
1 <= |a| <= (log(3x))^A,
f in F(1,K).
```

Notice: the **inner `q`-sum is signed and unweighted**. The theorem does not bound the sum of the absolute values of all its discrepancies.

### 4.1 Derivation for COMPLETE factor patterns

Partition the allowed primes above `y` into finitely many bins `I_j` whose endpoints satisfy the separation condition. Put

```
f_z(p)=z_j for p in I_j,
f_z(p)=0 for disallowed primes,
f_z(p^nu)=0 for nu>=2.
```

On the torus `|z_j|=1`, these functions are in `F(1,K)` with a fixed `K>=1`: they are bounded by 1, squarefree-supported and piecewise constant at primes. The coefficient of `product_j z_j^(k_j)` is EXACTLY the indicator of the prescribed full squarefree factorization pattern, with no leftover prime factors. Taking that coefficient by a normalized torus integral in the displayed dispersion estimate gives

```
| sum_d xi_d sum_q Delta_(E_pattern)(x;dq,a) |
 <= C x/(log(3x))^A
```

under precisely the same conditions. There is no coefficient-extraction loss on the unit circles. Taking one allowed bin gives the same result for `E_r` above, for any fixed `r`, including `r>2`. Finite smooth approximations to bins may also be assembled, but no such extension is needed for this corollary.

This is an unconditional consequence of a checked theorem, not an invented joint asymptotic. It is also not a claim of novelty: it records exactly the pattern information that the theorem permits us to extract.

### 4.2 The exact missing insertion

For two complete patterns, even without any CRT or sieve weight, the following identity shows the missing condition. With `E_0=1_{m=1}` and `s>=2`,

```
s * sum_{X<n<=2X} E_r(n) E_s(n+h)
 = sum_{p>y} sum_{X<n<=2X, n=-h mod p}
     E_r(n) E_(s-1)((n+h)/p) 1_{p not dividing (n+h)/p}.
```

Each squarefree `E_s` integer has exactly `s` choices of `p`, so this is exact. The dispersion corollary controls the inner arithmetic progression with weight `E_r(n)`, **not with the additional complementary-cofactor factor**

```
E_(s-1)((n+h)/p) 1_{p not dividing (n+h)/p}.
```

That factor is neither a coefficient depending only on the modulus `p`, nor a fixed multiplicative function of `n`. Removing it changes the statistic. Summing over more prime factors of `n+h` eventually leaves two prime cofactors subject to `A P+h=B Q`; ordinary prime or almost-prime distribution in APs does not count both simultaneously.

This is the precise unsupported inference in trying to promote the proved factor-pattern dispersion formula to the required two-coordinate estimate.

### 4.3 Why the Titchmarsh versions stop here

Drappeau–Topacogullari, arXiv:1807.09569, proves arbitrarily logarithmically accurate asymptotics for

```
sum f(n) tau(an-h),
```

where `|f|<=tau_A` and `f(p)` is periodic modulo a FIXED `D`; `a,|h|<=x^delta`. In particular it obtains full asymptotic expansions for

```
sum_{|h|<n<=x, omega(n)=k} tau(n-h),
```

uniformly for `k<<log log x`, with error

```
O(x (log log x)^k / [k! (log x)^(N+1-epsilon)]).
```

The exponent `N` is arbitrary. For fixed `k,D,Q=1`, error size is therefore not the principal problem: the second endpoint remains the ORDINARY divisor function, not an exact factor indicator or a rough-restricted divisor function.

The actual type-II lemma `lem:equidistrib-bilin` allows arbitrary divisor-bounded `beta,gamma` with the `gamma` component in `[X^eta,X^(1/3-eta)]`, and bounds

```
sum_{n in I} (beta*gamma)(n) Delta_h(an;R)
 << tau((a,h)) R^(-1/2) X (log X)^B,
```

for small power-sized `R,a,h`. Here `Delta_h` is the discrepancy for the ordinary shifted divisor function. In its proof, the opposite coordinate becomes an **unweighted** divisor-modulus sum `q<=sqrt(an-h)`. The lemma does not assert the same bound after replacing that function with a prime-factor-pattern restriction. This is where the complete divisor hyperbola, rather than a factor-pattern-resolved hyperbola, is used.

Similarly, in Fouvry–Tenenbaum the movable cutoff may be placed in `f` on the first coordinate; it does not authorize replacing `tau(n+h)` by `tau(n+h)R_y(n+h)`. Exact Möbius expansion of the latter roughness condition has long products of small primes. The theorem permits a short additional weighted modulus, not those arbitrary long products or their complementary-cofactor conditions. A sieve truncation does not come with a proved error negligible relative to the desired prime-pair difference.

## 5. Even ideal mixed divisor moments need not determine prime pairs

The following calculation tests information genuinely stronger than separate one-coordinate moments. Grant, hypothetically, exact rough-supported values of EVERY row and column marginal and of

```
sum_s 2^s N_rs   for every r,
sum_r 2^r N_rs   for every s.
```

On squarefree integers, `tau=2^Omega`, so these include the exact-count–divisor correlations in BOTH directions. Grant even their independence-benchmark values. This granting is used only to test logical sufficiency, not as an arithmetic assertion.

Take `eta=1/8`. The single-coordinate constants satisfy

```
a_1=1,
a_2=log 7 = 1.945910149055313305...,
a_3=(1/3) integral_(1/8)^(3/4)
                log((7/8-t)/(1/8))/(t(1-t)) dt
    =1.219127918172915197... .
```

There is a simple analytic bound, independent of numerical integration:

```
a_3 >= (log 3)/3 * integral_(1/8)^(1/2) dt/[t(1-t)]
    = (log 3 log 7)/3 > 1/2.
```

Also `a_2>3/2`. Let the benchmark table be `A_rs=a_r a_s`. Set `v=(2,-3,1,0,...)` and

```
C_rs = A_rs - (1/4) v_r v_s.
```

The altered 3-by-3 block is

```
[ 0,          a_2+3/2,          a_3-1/2          ]
[ a_2+3/2,    a_2^2-9/4,        a_2 a_3+3/4     ]
[ a_3-1/2,    a_2 a_3+3/4,      a_3^2-1/4       ].
```

Every entry is nonnegative. All other entries are unchanged. The numerical block is

```
[ 0,             3.445910149055, 0.719127918173 ]
[ 3.445910149055, 1.536566308196, 3.122313388969 ]
[ 0.719127918173, 3.122313388969, 1.236272880869 ].
```

Since

```
2-3+1=0,       2*2-3*4+1*8=0,
```

`C` has exactly the same row and column marginals as `A`, the same divisor-weighted row and column moments, and hence the same `tau x tau` moment. Nevertheless `C_11=0` while `A_11=1`.

Equivalently the generating-polynomial change is

```
-(1/4) z(z-1)(z-2) t(t-1)(t-2).
```

It vanishes on all four slices `z=1,2` and `t=1,2`, while changing the coefficient of `zt` by `-1`. Knowledge of the entire slices is not two-variable analytic continuation.

### Fully resolved ONE-side factor patterns do not remove this null direction

This example can be refined beyond factor counts. In each stratum `Omega=r`, distribute the signed mass `v_r` proportionally to the complete single-coordinate factor-pattern measure in that stratum. Call the resulting signed measure `v(dtheta)`. Then

```
integral v(dtheta)=0,
integral tau(theta) v(dtheta)=0.
```

Subtracting `(1/4) v(dtheta)v(dphi)` from the product-pattern measure preserves, for **every** measurable first-coordinate pattern set, its marginal and its mixed moment against the divisor function at the second coordinate. It does the same after interchanging coordinates. Nonnegativity reduces to exactly the block inequalities checked above. Thus refining the known side into arbitrarily fine factor-size patterns does not fix the information deficit.

This does NOT say that genuinely complete TWO-side pattern information is useless. For instance, the perturbation changes the `(3,3)` cell by `-1/4`; a sufficiently precise evaluation of that cell could distinguish these tables. All cells with either index at least 4 are unchanged. The checked total-pattern existence theorems provide neither such a rough-supported count nor such a weighted numerical constraint. The table is an information-obstruction certificate, NOT a counterexample model of the actual primes.

## 6. Error and conditioning checks on nearby candidates

### 6.1 CRT and weights are additional demands, not freely available

Drappeau–Topacogullari's implied constant depends on its fixed periodicity modulus `D` and is explicitly described as badly behaved with respect to `D`. Fouvry–Tenenbaum gives the more explicit error

```
C D^C_0 X/(log X)^A
```

and notes that the stated bounds allow `D` to grow at most like a bounded power of `log X` if a logarithmic saving is to be retained. Encoding a CRT condition by characters modulo `Q` would bring in `D=Q`. Relative to an `X/(Q log^2 X)` pair scale this upper bound has ratio, apart from local factors,

```
Q^(C_0+1) (log X)^(2-A).
```

`Q=X^{o(1)}` by itself does NOT make that tend to zero. In the efficient covering construction `Q` may be much larger than every fixed logarithmic power. The small-cofactor issue already blocks the argument with `Q=1`; this is a further, separately tracked obstacle to an actual application.

The signed inner modulus average in the dispersion theorem also cannot simply be replaced by the CRT-dependent residues or the correlations produced after expanding a Maynard weight. No such extension is claimed.

### 6.2 Bivariate Erdős–Kac is not a rare-pattern local limit theorem

Mangerel, arXiv:1612.09544, theorem `EKTHM`, assumes a fixed shift and a siftable regular set `S`, including

```
# {n<=X: n,n+h in S, (n,h)=1} >>_h X,
```

and gives an absolute distribution-function error

```
O(log_3 X / (log_2 X)^(1/4)).
```

Power-rough endpoint pairs do not meet the positive-density hypothesis. Even outside that support issue, this absolute error is vastly larger than the probability of fixed small factor counts. Fixed `r,s>2` are not the central-limit range `r,s~log log X`.

Fouvry–Tenenbaum also has an Erdős–Wintner theorem conditioned on `omega(n-1)=k`, but the additive function on the other coordinate must satisfy the three convergent-prime-series conditions. Taking it to be total `Omega` or `omega` violates those conditions. Taking a cutoff-dependent function requires uniformity in that family, not the fixed-function limiting statement. Its conditional Erdős–Kac theorem likewise gives an absolute `o(1)`, not a relative rare-cell estimate.

### 6.3 Genuine higher-divisor correlations averaged over shifts

Matomäki–Radziwiłł–Tao, arXiv:1712.08840, does evaluate both divisor coordinates on average, but its main theorem requires

```
(log X)^(10000 k log k) <= H <= X^(1-epsilon),  k>=l>=2,
```

and its error is `o(H X log^(k+l-2) X)` (or `o(H X log^(k-1) X)` for `Lambda x d_k`). It is not an estimate for a prescribed `h~C log X` or a thin `O(log X)` band, and its error is not `o(HX/log^2 X)` after coefficient extraction. Moreover its typical-factor truncation requires factors in certain polylogarithmic/subpower intervals; power-rough numbers are outside that typical set. One cannot reuse its negligible-complement estimate relative to the much smaller rough-support mass.

None of Evans's correlation ranges, the common-cofactor localization discussed in the task, or a raw multiplicative cancellation estimate was substituted for the missing bound.

## 7. Verification and source locations

The following statements are independent of all prime-gap assumptions:

- The finite table identities and its nonnegativity under `a_2>=3/2`, `a_3>=1/2` are checked in Lean in `Submission/JointPatternAudit.lean`.
- `Submission/check_joint_pattern_audit.py` checks the exact rational perturbation with SymPy, integrates the one-coordinate `a_3` constant with mpmath, checks the analytic lower bound numerically as a cross-check, and verifies the unchanged Spec hash and two original `sorry` occurrences. The proof of the bound itself is the explicit integral inequality above, not the floating-point test.
- No file added by this investigation imports `Submission.Spec`, states an extra axiom, or uses either original `sorry` theorem. The Lean audit uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

Relevant source locations (line numbers in the local source files):

- `1710.01195/binary_correlations_arxiv2.tex`: uniformity hypothesis and main theorem 33–58; exact joint large-factor theorem 103–109; smooth-cofactor integral and coefficient extraction 681–750.
- `0803.2636/0803.2636.tex`: total-count and exponent-pattern theorems 213–258; Basic Theorem and illustrating relation coefficients 272–355; shift-2 counts 366–381.
- `2003.03661/2003.03661.tex`: Basic Theorem/adjoining primes 39–89; mechanism and first pattern theorem 113–135; remaining pattern 299–302.
- `2004.04766/BV-2021.tex`: discrepancy definition 44–47; function class 219–240; central theorem and corollaries 329–378; Titchmarsh use of the unweighted divisor sum 417–440; conditional distribution hypotheses 443–510.
- `1807.09569/divtm-alpha.tex`: function class and main theorem 50–93; status/scope of higher-divisor correlations 118–154; exact-count–divisor expansion 223–246; type-II statement and unweighted opposite divisor sum 868–904.
- `1612.09544/ChowlaFin.tex`: rare-count caveat 120–135; siftability/positive-density hypotheses and quantitative theorem 188–229.
- `1712.08840/intro.tex`: theorem, error, and averaging limitations 35–70; `fourier.tex`: typical-factor support and removal estimate 106–128.
- `1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`: efficient covering lemma 2072–2121.

## Conclusion

The focused route does expose genuinely stronger arithmetic than the previously considered one-coordinate sieve marginals. Complete factor-pattern coefficients can be extracted from a proved dispersion result with arbitrarily many logarithmic savings, and joint exact LARGE-factor counts have a genuine independence theorem. Neither result evaluates the complementary cofactor under the other endpoint's exact pattern or primality condition.

The exact missing inference is the promotion of an unweighted divisor-modulus average, or a positive-density large-factor statistic with free smooth cofactor, to the same-translate, two-coordinate complete-factor-pattern count on power-rough/CRT support. The displayed cofactor identity identifies the extra factor that has no proved estimate; the boundary calculation tracks its density scale; the nonnegative completion shows that retaining only the available mixed divisor projections cannot algebraically fill the gap.

Therefore no positive lower bound for the required prime–prime block sum, no improvement of the pair-upper-bound constant to the necessary range, and no proof of `Erdos5.erdos_5` follows from this attempt.
