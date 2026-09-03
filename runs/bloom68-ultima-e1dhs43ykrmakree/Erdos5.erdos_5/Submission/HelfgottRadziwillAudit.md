# Helfgott–Radziwiłł route: operator, iteration, and cofactor audit

## Outcome

**No unconditional proof or disproof of Erdős #5 was obtained.** In particular, this attempt did not prove simultaneous prime occupancy of the two CRT endpoint groups. No Lean theorem was added, and `Submission/Spec.lean` was neither edited nor used as a premise. Its original SHA-256 is

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

The calculations below test the proposed mechanism, rather than assuming a relative parity estimate or adding another sufficient-condition theorem. They include an exact transport identity for cofactor marks, its actual two-step replacement, quantitative error budgets, and an arithmetic calculation for a proposed composite-edge repair.

## 1. What the checked sources actually supply

Sources inspected:

* `/corpus/src/2103.06853/trace.tex`, corpus version v2: operator and Main Theorem, lines 186–238; normalized `L^4` corollary `cor:maic`, lines 244–265 and proof 5790–5868; factor-count transport `cor:cruxio`, lines 325–384 and proof 6442–6556; composite-length proposals, lines 7505–7562.
* `/corpus/src/2201.00799/CANT_Expansion.tex`: multiplicative transport, lines 116–167; repeated Cauchy–Schwarz, lines 184–259; operator/powers, lines 638–737; concluding theorem, lines 1691–1703.

The second paper is explicitly an exposition, not a second independent endpoint-conditioned theorem. Its concluding theorem prints exponent `1/2` in the lower bound on `log H_0`; the checked full-proof version prints `2/3`. All parameter choices below satisfy the stricter `2/3` condition.

Let `V=(N,2N]`, and use normalized counting inner products. Write

```
D f(n) = sum_{p in P, sigma=+-1, n+sigma*p in V} 1_{p|n} f(n+sigma*p),
T f(n) = sum_{p in P, sigma=+-1, n+sigma*p in V} f(n+sigma*p)/p,
A = D-T,       L = sum_{p in P} 1/p.
```

The Main Theorem assumes

```
log H_0 >= (log H)^(2/3) (log log H)^2,
L >= e,   log H <= sqrt(log N/L),
1 <= K <= log N / (L (log H)^2).
```

It supplies a set `X_good` with

```
|V \ X_good| << N exp(-K L log K) + N/sqrt(H_0),
||A restricted to X_good|| <= C_0 sqrt(K L).
```

The full-vertex bilinear corollary allows `||f||_2,||g||_2 <= 1` and
`||f||_4,||g||_4 <= exp(C L)`, provided `(32C+4)L <= log H_0`. Its normalized discrepancy is `O_C(L^(-1/2))`.

**Thus “the functions are sparse” is not, by itself, a valid objection.** For example, set

```
t = log log N,
log H = (log N)^(2/5),
log H_0 = (log N)^(3/10),
P = all primes in [H_0,H].
```

Then `L=(1/10+o(1))t`, the upper limit on `K` tends to infinity, and any desired fixed inverse-logarithmic exceptional density is obtained by choosing a sufficiently large **fixed** `K`. A normalized indicator of density `(log N)^(-a)` has `L^4` norm `(log N)^(a/4)=exp(O_a(L))`, so it is permitted. One need not discard all unconditioned power-rough support in this application. Much thinner CRT support is a separate issue.

## 2. Centered powers really are small; transport powers are different

Compress all three operators to the *same* good set, and put

```
U=D/(2L),   Q=T/(2L),   E=U-Q,   eta=C_0 sqrt(K/L)/2.
```

Then `||Q||<=1`, `||E||<=eta`, and, for every integer `k>=1`,

```
||E^k|| <= eta^k.
```

There is no restriction to the moment orders used in the proof once the operator norm has been obtained. With fixed `K` and `L~t`, taking `k` of order `t/log t` really can make this smaller than a specified power of `1/log N`. For example, `eta^k < (log N)^(-2)` requires `k>(4+o(1))t/log t`. This numerical part of the proposed amplification works.

But the exact noncommuting identity is

```
U^k-Q^k = sum_{j=0}^{k-1} U^(k-1-j) E Q^j,
||U^k-Q^k|| <= (1+eta)^k-1,
```

not `U^k-Q^k=E^k`. The first-order error remains. Likewise, for a unit vector `f`,

```
|<f,E f>| <= <f,E^(2k) f>^(1/(2k)) <= eta.
```

Using higher moments to bound the original correlation takes back the root; it does not give `eta^k` for that correlation.

The exact path expansion has vertices `n_j=n+sum_{i<=j} sigma_i p_i` and weight

```
product_{i=1}^k (1_{p_i|n_(i-1)}-1/p_i),
```

with every `n_j` in the good set. It involves **additive** path displacements, not multiplication of the original endpoints by `p_1...p_k`.

Already for the uncentered `D^2`, a path with distinct labels `p,q` has the unique parametrization

```
start = p(qr-sigma),   midpoint = pqr,   end = q(pr+tau).
```

For Liouville endpoint weights its product is

```
lambda(qr-sigma) lambda(pr+tau).
```

For prime-cofactor marks the corresponding endpoints are marked at `qr-sigma` and `pr+tau`. These are different affine forms with different coefficients, not the original nearby pair. When `p=q`, the endpoints instead reduce to `m` and `m+sigma+tau`. Those repeated-label paths have only one divisibility condition and reciprocal mass `L`, not `L^2`. They cannot be treated as two independent transports.

Also, `A^2=D^2-DT-TD+T^2`: a small bound for this signed combination does not separately bound its desired repeated-label component. Inserting endpoint/interior masks during iteration introduces the masks at additional path vertices, hence further joint correlations.

## 3. What happens on the actual rough support

Let `R` denote multiplication by the indicator of integers with least prime factor greater than `y`, with `y>H`. Since `p|n` iff `p|n+-p`,

```
D R = R D = 0,
A R = -T R,
R A^2 R = R T^2 R.
```

The same identities hold after the good-set compression. When all `p` are odd and `y>2`, also `R A R=0`, since rough vertices are odd. Thus direct divisibility transport on this support is absent; the square controls an additive convolution through intermediate vertices, not a prime–rough parity transport. In general `R A^k R` is not `(-1)^k R T^k R`: interior divisibility terms return.

The norm bound is valid for every coloring of the rough vertices by signs. A conclusion specifically about `lambda` there therefore needs the arithmetic transport identity, not just the norm.

For reference, if two bounded functions have support densities `delta_f,delta_g`, the one-step normalized norm budget is

```
O(sqrt(delta_f delta_g)/sqrt L).
```

For two densities `1/log N`, this is `1/(log N sqrt L)`, larger than the pair-count benchmark `1/log^2 N` by `log N/sqrt L`. These are comparisons of available error bounds, **not assertions of a prime-pair asymptotic**. Putting the already-joint endpoint event into a mask does not solve this: transporting that mask is itself an additional arithmetic assertion.

## 4. An exact cofactor lift, and its norm cost

Here is a lift that genuinely repairs the elementary identity `R_y(pm)=0` for small `p`.

Let `a,b` be any functions supported on `y`-rough integers, and define

```
F(n)=sum_{p in P, p|n} a(n/p),
G(n)=sum_{p in P, p|n} b(n/p).
```

There is at most one nonzero summand in either lift: its integer has exactly one small prime factor, to exponent one. For an integer shift `h`, define `D_h` by replacing the step `+-p` in `D` with `+-hp`. Then, exactly, with both endpoints required to belong to `V`,

```
sum_n F(n) sum_{p|n, sigma} G(n+sigma*h*p)
  = sum_{p,sigma} sum_{m: pm, p(m+sigma*h) in V} a(m)b(m+sigma*h).
```

This can encode an arbitrary row weight inside `a`. **The displayed source norm is for `D_1-T_1`, not for this entire family with growing `h` and CRT conditions.** Even granting the same bound for the required `h` does not give the desired relative estimate:

* For `a=1_Prime` and `b=R_y lambda`, with `y=N^theta`, `1/3<theta<1/2`, single-integer prime/rough counts give
  `||F||_2^2 ~ L/log N` and `||G||_2^2 asymp L/log N`.
* The normalized discrepancy budget is consequently `O(sqrt L/log N)`.
* Against `1/log^2 N` this loses a factor `log N sqrt L`.

For `h=1` both rough cofactors cannot occur together because of ordinary even/odd parity; the identity is then zero, not a prime-pair theorem. The even-shift problem requires the appropriate different transport, or the path components discussed above. This distinction is not suppressed in the error comparison.

Choosing cofactor coefficients does not improve the `L^2` ratio. If the two lifts have coefficients `u_p,v_p` and `alpha=sum_p u_p v_p/p`, their norm product is, up to fixed single-integer constants,

```
(1/log N) sqrt(sum_p |u_p|^2/p) sqrt(sum_p |v_p|^2/p)
  >= |alpha|/log N.
```

The true transported pair benchmark has the factor `alpha/log^2 N`. Thus the same norm method still has the `sqrt L log N` loss. This is a limitation of the **available upper-bound budget**, not a lower bound on the actual arithmetic discrepancy.

A source-valid variant with an unrestricted Liouville endpoint takes `G=-lambda`; the actual `D_1` identity then transports `1_Prime(m)lambda(m+-1)`. Its norm budget is `O(1/sqrt(log N))`, whereas the prime-conditioned mass is only of order `1/log N`. It supplies no relative sign estimate.

### A multiplicative generating-function repair also has an explicit cost

Let `s_y(n)` be the entire `y`-smooth part and `r_y(n)=n/s_y(n)`. Consider

```
f_z(n)=z^Omega(s_y(n)) 1_Prime(r_y(n)),
g_z(n)=z^Omega(s_y(n)) lambda(r_y(n)) 1_{r_y(n)>1}.
```

For every `p in P`, both satisfy `f_z(pm)=z f_z(m)` and `g_z(pm)=z g_z(m)`. For analytic coefficient extraction use the bilinear form, applying the source's Hermitian inequality to `f_z` and the complex conjugate of `g_z`. This is a **real transport identity for the whole family**. Its true-edge bilinear sum equals `z^2` times the corresponding cofactor correlation. The coefficient of `z^2` recovers the zero-small-factor prime–rough correlation; it does not arise from evaluating a dense estimate at `z=0` without a cost.

For `|z|=r<=1/2`, uniformly also near the optimizing radius, single-integer counting gives

```
||f_z||_2^2 asymp (log N)^(r^2-1),
||g_z||_2^2 asymp (log N)^(r^2-1).
```

One way to check this is to sum over the unique smooth cofactor `a`. The harmonic sum is bounded above by, and retains a fixed positive fraction of,

```
sum_{a y-smooth} r^(2 Omega(a))/a
  = product_{p<=y}(1-r^2/p)^(-1) asymp (log y)^(r^2).
```

Indeed, its normalized mean of `log a` is `(r^2+o(r^2)) log y`, uniformly for `0<r<=1/2`; restricting to `a<=N^beta` for a suitable fixed `beta<1-theta` retains a fixed fraction (the case `r=0` is immediate). PNT for the complementary prime supplies `1/log N`. The rough complementary factor has the same order, by its prime lower bound and prime-plus-semiprime upper bound.

Cauchy coefficient extraction costs `r^(-2)`. Even with the favorable analogous operator norm, its normalized error budget is therefore

```
O((log N)^(r^2-1)/(r^2 sqrt L)).
```

Writing `t=log log N`, this is minimized at `r^2=1/t`, giving

```
O(t/(sqrt L log N)),
```

again of order `sqrt(t)/log N` when `L~t`, rather than `o(1/log^2 N)`. The normalized `L^4` allowance is compatible with this calculation; it does not remove the coefficient-extraction cost. No uniform CRT or growing-shift theorem is being inferred from this computation.

## 5. Testing composite dilations instead of additive paths

Composite dilation would preserve the multiplicative identity, but it is not `A^k`. There is an elementary arithmetic obstruction to the simplest proposed replacement.

Take disjoint prime sets `P_1,P_2` up to `H=N^o(1)`, with reciprocal sums `ell_1,ell_2 asymp ell -> infinity`, and define

```
A_cross f(n)=sum_{p in P_1,q in P_2,sigma}
             (1_{pq|n}-1/(pq)) f(n+sigma*pq).
```

Put `B_i(n)=# {p in P_i:p|n}` and `v_i=sum_{p in P_i}(1/p)(1-1/p)`. Away from interval boundaries,

```
A_cross 1(n)=2(B_1(n)B_2(n)-ell_1 ell_2).
```

CRT counting of moments, with an `O(H^4/N)` rounding error, gives

```
E[(B_1 B_2-ell_1 ell_2)^2]
  = ell_1^2 v_2 + ell_2^2 v_1 + v_1 v_2 + O(H^4/N).
```

Thus `||A_cross|| >> ell^(3/2)`, not `O(ell)`, although the average degree is of order `ell^2`. The boundary error in the squared calculation is `O(H^6/N)`.

This lower bound also survives restriction to **any** set with complement density `delta=o(1/ell)`. Test against `f=B_1-ell_1` and `1`. Their full bilinear form is `2 ell_2 v_1+o(1) ~ ell^2`, and `||f||_2=O(sqrt ell)`. If `M` is the nonnegative operator with each edge weight replaced by `1_{pq|n}+1/(pq)` and row sum `w`, then

```
||f||_4=O(sqrt ell),   ||w||_4=O(ell^2),
||M f||_2 <= ||f||_4 ||w||_4.
```

The last inequality follows from Cauchy–Schwarz, symmetry, and `ab^2<=(a^3+2b^3)/3`. Removing the bad endpoints changes the bilinear form by at most `O(sqrt(delta) ell^(5/2))`, which is `o(ell^2)`. All needed divisor moments have fixed degree at most eight and follow from the same CRT calculation.

So merely multiplying the available degree does **not** multiply the spectral saving. One could instead fully center the composite edge by

```
(1_{p|n}-1/p)(1_{q|n}-1/q).
```

That removes the displayed first-order divisor-count fluctuations, but gives a new operator with displacement `pq`; it is not the composition of two prime-edge operators, whose displacement is `+-p+-q`. Its expansion and the partially divisible terms in its transport are not supplied by either paper.

There is also a growing-order normalization check. For products of `k` distinct primes from one pool, summing over **ordered** tuples repeats each composite edge `k!` times. The fully centered composite operator then has, under `H^(2k)(k!)^2=o(N)` and `k/H_0+k^2/(H_0 L)=o(1)` (both hold for the displayed parameters and `k=O(t/log t)`),

```
Tr(B_k^2)/N ~ 2 k! L^k,
||B_k|| >= (1-o(1)) (2 k!)^(1/2) L^(k/2).
```

This follows by averaging the square of an edge weight: each prime contributes `(1/p)(1-1/p)`. Equivalently, unordered products have harmonic degree approximately `L^k/k!`, not `L^k`. Treating these composite dilations as additive path powers loses a factorial factor at precisely the growing `k` under consideration. This does not contradict the genuine bound on `A^k`; it shows that the proposed replacement is a different operation.

## 6. Gap geometry and the CRT condition still have to be retained

If `u,v in [X,2X]`, `|v-u|<=D`, and `a,b<=M`, then for `a!=b`,

```
|bv-au| = |(b-a)u+b(v-u)| >= X-MD.
```

Consequently, if `MD+kH<X`, a path of length `k` with steps at most `H` between such lifted endpoints must have **the same cofactor**. Its displacement is then `a(v-u)`. For a nonzero target gap and `k` of the proposed size, the common cofactor allowed by locality is subpower-sized, not a dense cofactor lift. In fact, for `M=N^o(1)`, the density of integers `n~N` with `n/a` prime for some `a<=M` is of order `log(2M)/log N=o(1)`. The representation is unique when `M^2<N`; summing the single-prime count proves the assertion.

There is an exact small-part version. Along a true edge `n=pm`, `n+hp=p(m+h)`,

```
s_y(n)=p s_y(m),   s_y(n+hp)=p s_y(m+h).
```

If these two smooth parts are equal to `a`, then `a/p` divides `h`, because it divides both `m` and `m+h`. For `h=1` this forces `a=p`; for two genuinely rough cofactors it also forces `a=p`. The dense lift obtained by allowing arbitrary smooth cofactors has mostly changed the cofactor, not preserved the desired endpoint pair.

A CRT/interior mask cannot be commuted through the operator for free. Exactly,

```
[A,M_W]f(n)=sum_{p,sigma}(1_{p|n}-1/p)
             (W(n+sigma*p)-W(n)) f(n+sigma*p).
```

For a fixed row class modulo `Q>H`, the difference of masks is generally of size one, not a small error. If `kH<Q`, return to that class forces an exact displacement condition, not free mixing among CRT rows. The optimized exceptional-set observation in section 1 only handles fixed inverse-logarithmic densities automatically; it is not a distribution theorem on a class of density `1/Q` with much larger `Q`.

Finally, for endpoints in `(X,3X]` choose `(3X)^(1/3)<y<X`, as in the power-rough setup. Every rough endpoint then has `Omega=1` or `2`, including squares correctly. Hence

```
1_Prime = R_y (1-lambda)/2.
```

For a nonnegative same-row/CRT/interior weight `W`, put

```
M = sum_m W(m) 1_Prime(m) R_y(m+h),
J = sum_m W(m) 1_Prime(m) R_y(m+h) lambda(m+h).
```

The desired weighted prime–prime count is exactly `(M-J)/2`. **The attempt has not proved the relative upper bound on `J` needed to make this positive, nor the same-row two-block occupancy.** The unconditioned prime fraction among rough numbers was not transferred through this conditioning. The calculations identify why the tested transports and norm powers do not yet supply that estimate; they do not prove that every possible expansion-based approach must fail.

## Verification

Exact finite, rational-arithmetic checks were run for the rough-support compressions, the noncommuting telescoping identity through power four, the complete two-step cofactor parametrization, unique-small-prime lifts at shifts `1,2,6,10`, the shared-smooth-cofactor divisibility assertion, and the product-divisor variance polynomial. These are checks of algebraic identities, not numerical prime-gap searches or tests of asymptotic expansion. The asymptotic estimates above were checked separately against their single-integer counting and moment arguments. No proof completion is claimed.
