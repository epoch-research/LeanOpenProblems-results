# Erdős 371: full-partition conservation does not determine the ordering current

## Result and scope

**This does not prove or disprove Erdős 371.** It gives an explicit countermodel to the proposed *partition-level* linearization, substantially stronger than an equal-marginals or first-moment counterexample.

There is a deterministically specified, positive coupling `Q` of two **complete PD(1) mass partitions** `A,B` such that:

1. Both partitions sum to **exactly 1**, almost surely; both entire marginal laws are exactly PD(1).
2. Every mixed factorial correlation agrees with the independent law whenever the total mass of the selected parts is at most **21/20**, not just below 1.
3. Consequently all the usual subcritical CRT limiting correlations hold, at every order. The complete mass-conservation hierarchy and all its iterations hold as well.
4. Nevertheless
   ```
   E_Q sgn(max B - max A) > 10^(-5).
   ```
   There are no ties. Transposing Q gives the opposite bias with exactly the same specified data.
5. Q has density between `1/2` and `3/2` relative to the independent PD law. Thus the obstruction is not singular support, missing small factors, atoms on the diagonal, or an incorrect marginal law.

The construction uses bounded signed multiplicative functionals whose **residual-mass partition functions have compact support**. It exhibits a nonzero homogeneous solution of the mass-conservation equations with zero subcritical boundary data.

An additional literal, finite deterministic countermodel is a 576-edge periodic word of mass-one partitions. It preserves every factorial test through total selected mass 1 and has signed ordering mean `1/72`. Unlike the PD model, that finite example has discrete marginals and ties; it is an exact algebraic certificate, not a substitute for the stronger PD construction.

No Lean file was opened, used, or edited, and in particular no use was made of `Spec.lean`. The earlier Alladi/long-modulus reductions in `RoughOddMomentResearch.md` and `ReflectionResearch.md` are not being rederived here.

**Important limitation.** The countermodel satisfies the limiting **log-partition** data supplied by subcritical CRT; it is not a model of actual consecutive integers or of individual modular-inverse endpoint errors. It rules out a deduction from those partition data and conservation alone. It does not rule out a new arithmetic input, or an estimate involving growing-order, non-uniformly-integrable divisor expansions that is stronger than the specified limiting correlations.

## 1. Precisely which data are retained?

Write a mass partition as `A=(a_i)`, with `a_i>0` and `sum_i a_i=1`. Let `mu=PD(1)`. For an ordered selection of distinct indices, its factorial density is

```
rho_k(x_1,...,x_k) = 1/(x_1 ... x_k),  s:=sum x_i<1.      (1)
```

It vanishes for `s>1`. Conditional on the selected parts, the remaining partition has law `(1-s) PD(1)`. This is the factorial Palm statement, not conditional independence between A and B.

For two partitions define the mixed factorial observable

```
T_phi(A,B) = sum_{i_1,...,i_k distinct; j_1,...,j_l distinct}
                phi(a_{i_1},...,a_{i_k};b_{j_1},...,b_{j_l}).
```

The test function is bounded and compactly supported away from zero; arbitrary such measurable tests can be used. The proposed CRT data are

```
E T_phi = integral phi(x;y) dx dy / (prod x_i prod y_j),  (2)
```

when `s+t<1`, where `t=sum y_j`.

These are precisely the fixed-order log-prime selection data obtained from coprime products `d|n`, `e|n+1`, `de<X`, away from the critical boundary. Repeated macroscopic primes and shared macroscopic primes disappear in this limit. Prime powers can instead be included in the original mass partitions; they do not alter the limiting PD law.

The countermodel preserves more than (2): the entire marginals, and (2) on `s<1,t<1,s+t<=21/20`. For arbitrary tests on that region the correction density vanishes pointwise. There is no finite-order truncation in this assertion.

Corpus check: the PD factorial formula and its conditional scale-invariant-Poisson explanation are in `/corpus/src/1401.1555/bt.tex`, lines 451–542, particularly the formula labelled `PD 1 multi intensity`. The construction below is derived here and needs no prime-pair independence assertion.

## 2. Bounded signed functionals with compact residual-mass support

For `0<=u<=20/9`, define explicitly

```
a(u) = 2-exp(u)
       +1_{u>=1} u exp(u-1)
       +1_{u>=2} (u-u^2/2) exp(u-2).                    (3)
```

The value at the single jump `u=1` will not matter for PD expectations. Use the right value there. The function is continuous at 2.

Let

```
c=9/20,  d=1/2,
f_c(x)=a(x/c),  f_d(x)=a(x/d),
F_c(t)=(1-t/c)_+,  F_d(t)=(1-t/d)_+.
```

### Exact renewal identity

For either `b=c` or `b=d`, and `0<=t<=1`,

```
t F_b(t) = integral_0^t f_b(x) F_b(t-x) dx.              (4)
```

Here is a direct verification, including the support cutoff. In units `u=t/b`, on `0<u<1` one has `a(u)=2-exp(u)`, and

```
integral_0^u (2-exp(v))(1-u+v) dv = u(1-u).
```

For `u>1`, (3) satisfies, on each smooth interval,

```
a'(u)=a(u)-a(u-1),
a(1+)=3-e=integral_0^1 a(v)dv.
```

Together with continuity at 2 this gives

```
a(u)=integral_{u-1}^u a(v)dv.                            (5)
```

Therefore `I(u)=integral_{u-1}^u a(v)(1-u+v)dv` has derivative zero and `I(1)=0`. This proves (4) also when its right-hand side must vanish.

Moreover

```
|a(u)|<=1  (0<=u<=20/9),   a(u)=1-u+O(u^2) near zero.    (6)
```

For (6), first use `2-exp(u)` on `[0,1)`. After the jump, (5) is an average over a unit interval. A first strict maximum of `|a|` above 1 would be strictly larger than that average, a contradiction. This also proves the bound without numerical estimates of the exponential-polynomial pieces.

For every mass partition set

```
h_b(A)=prod_i f_b(a_i).                                 (7)
```

The infinite product exists: near zero `1-f_b(x)=O(x)` and `sum a_i=1`; only finitely many factors lie outside any fixed neighborhood of zero. It satisfies `|h_b|<=1`.

### Its complete partition function is known exactly

For `A~PD(1)`,

```
E_mu prod_i f_b(t a_i) = F_b(t),  0<=t<=1.               (8)
```

One does not have to assume uniqueness of a singular Volterra equation. Use the size-biased GEM representation: its first part is uniform on `(0,t)` and the residual is an independent scaled PD partition. Equation (4) can be iterated along this stick breaking. The residual mass tends to zero, `F_b(0)=1`, and all products are bounded by 1. Dominated convergence yields exactly (8).

In particular,

```
E_mu h_c = E_mu h_d = 0.                                (9)
```

The factorial Palm formula now gives the **entire** tilted factorial hierarchy:

```
H_{b,k}(x_1,...,x_k)
  := density of E_mu[h_b(A) sum_distinct delta_(a_i)]
   = (prod_i f_b(x_i)/x_i) F_b(1-s),  s<1.              (10)
```

Consequently it is identically zero if `s<=1-b`. These are bounded, nonzero modes invisible to every selected subpartition of sufficiently small total mass. They are not merely functions with a vanishing first moment.

## 3. The positive coupling and all subcritical cancellations

Define Q by the deterministic density

```
dQ(A,B) / d(mu x mu)
 = 1 + (1/4)[h_c(A)h_d(B)-h_d(A)h_c(B)].                 (11)
```

By (6)–(9) this is a probability density in `[1/2,3/2]`, and both full marginals are exactly mu.

The correction to its mixed factorial density is exactly

```
(1/4)[H_{c,k}(x) H_{d,l}(y)
      -H_{d,k}(x) H_{c,l}(y)].                          (12)
```

The first product can be nonzero only if

```
s>11/20 and t>1/2,
```

and the second only if the two inequalities are reversed. Thus (12) vanishes identically throughout

```
s+t <= 21/20.                                          (13)
```

This proves the claimed all-order CRT matching, with a fixed margin beyond the critical line.

### Full conservation is retained, not just a first moment

For example, the signed correction densities D obey

```
(1-s) D_{k,l}(x;y)
 = integral_0^(1-s) z D_{k+1,l}(x,z;y) dz,              (14)
```

and the analogous equation on B. This follows either pointwise from the exact mass-one support or directly from (4) and (10). Every iteration, linear consequence, and valid integrable limit of these conservation identities holds in Q.

So (12) is a nonzero homogeneous solution of the *complete* conservation hierarchy, with zero data on (13). A proposed strict positive contraction deduced from just those data cannot establish uniqueness: Q and its transpose already supply different solutions.

## 4. A rigorous nonzero largest-part ordering current

Let `M(A)=max_i a_i`, and let `nu_b` be the signed law of M under `h_b dmu`. Thus `nu_b((0,1])=0`. Define

```
B = integral integral sgn(y-x) nu_c(dx) nu_d(dy).         (15)
```

Antisymmetry gives

```
E_Q sgn(M(B)-M(A)) = B/2.                               (16)
```

We now verify `B>2*10^(-5)`. This step is important: nonzero hidden joint modes alone would not show that the *particular ordering statistic* detects one.

### 4.1 Explicit densities above 1/3

For `1/3<t<1/2`, at most two parts exceed t. Inclusion-exclusion therefore terminates after two parts, and (10) gives the signed largest-part density

```
r_b(t) = - f_b(t)/t * integral_t^(1-t)
                  f_b(y)/y * (1-(1-t-y)/b) dy.           (17)
```

The single-part term has derivative zero in this range, because `F_b(1-t)=0`. For `1/2<t<1`,

```
r_b(t) = f_b(t)/t * (1-(1-t)/b)_+.                      (18)
```

These are low-dimensional, explicitly evaluable formulas, not a long-modulus arithmetic reduction.

Write `q=1/3` and

```
B_high = integral_{q<x,y<1} sgn(y-x) r_c(x)r_d(y) dxdy.
```

A certified piecewise-linear integration gives

```
0.00003718379989416998 < B_high < 0.00003767762705466383. (19)
```

The error bound is analytic, not an observed agreement of numerical runs. Details and the exact rational certificate are in §5.

### 4.2 Bound the omitted region without computing it

Because both nu's have total mass zero, the two cross rectangles

```
x<=q<y   and   y<=q<x
```

cancel **exactly** in (15). Hence

```
|B-B_high| <= ||nu_c restricted to (0,q]||_TV
              * ||nu_d restricted to (0,q]||_TV.         (20)
```

For `x<=q` and either b, `u=x/b<=20/27<3/4`. The elementary inequality

```
|2-exp(u)| <= exp(-u)
```

holds in this range. (For the negative branch, use `exp(3/4)<9/4<1+sqrt(2)`.) Thus `|h_b|<=exp(-1/b)` whenever `M<=q`.

If also `M>1/4`, its largest factor improves this by

```
R_b = max_{1/(4b)<=u<=1/(3b)} |2 exp(u)-exp(2u)|.
```

This function decreases to zero and then increases, so the maximum is at an endpoint. Elementary exponential bounds give

```
R_c<9/20,  R_d<29/50,
exp(-20/9)<109/1000,  exp(-2)<17/125.
```

The PD largest-part law is Dickman's: `Pr(M<=1/u)=rho(u)`. We use only

```
rho(3)<1/20,  rho(4)<1/80.
```

The first is certified by a monotone right Riemann sum for

```
rho(3)=1-log(3)+integral_1^2 log(v)/(v+1) dv.
```

The second follows without another numerical integral from
`4 rho(4)=integral_3^4 rho(v)dv<=rho(3)`.

Splitting at `M=1/4` yields

```
||nu_b restricted to (0,1/3]||_TV
 <= exp(-1/b)[R_b rho(3)+(1-R_b)rho(4)].
```

In particular the two bounds are respectively

```
5123/1600000,   2329/500000.
```

Their product is

```
11931467/800000000000 = 0.00001491433375.                 (21)
```

Combining (19)–(21) proves

```
B > 0.00002226946614416998 > 2*10^(-5),
E_Q sgn(M(B)-M(A)) > 0.00001113473307208499 > 10^(-5).  (22)
```

Since Q is absolutely continuous relative to independent PD, ties have zero probability. Thus its ascent probability exceeds `0.500005`. This is a statement about the countermodel, **not** about the integers.

## 5. Audit of the numerical certificate in (19)

The accompanying `FullPartitionVerification.py` is reproducible with Python 3, Decimal, and SymPy. Its integral certificate does not rely on SciPy, Monte Carlo, or unbounded black-box integration error estimates.

### Regularity bounds

On each smooth interval, for b=c,d,

```
|r_b(t)|<=3,    |r_b''(t)|<=1000,   1/3<=t<=1.           (23)
```

All nonsmooth points are among

```
1/3, 9/20, 1/2, 11/20, 9/10, 1.
```

For completeness, below 1/2 put `w(t)=f_b(t)/t` and let J be the integral in (17). On the relevant intervals, (3) gives `|a'|,|a''|<=3`, so

```
|w|<=3, |w'|<=29, |w''|<=220,
|J|<=log(2)<0.7, |J'|<=7, |J''|<=85.
```

Indeed

```
J'  = -w(1-t)-w(t)(1-(1-2t)/b)+(1/b)int_t^(1-t) w(y)dy,
J'' = w'(1-t)-w'(t)(1-(1-2t)/b)
      -(1/b)w(1-t)-(3/b)w(t).
```

These imply `|r''|<815`. Above 1/2, use
`r=a(t/b)[1/b-(1-b)/(bt)]` on its active range. The delay identity gives `|a'|<=2, |a''|<=5` away from the listed break points; the bound is then less than 115. This proves (23).

### Rational interpolation and its exact integral

Use the uniform grid `i/30000`, from `i=10000` to `30000`. It includes every break point. At the jump `t=9/20`, retain the correct one-sided values separately.

For the true-node piecewise-linear interpolant R,

```
||r-R||_1 <= (1000/18)/30000^2.
```

Both r and R have L1 norm at most 2. Therefore the change in the antisymmetric bilinear ordering form is at most

```
4*(1000/18)/30000^2 = 1/4050000.
```

The node values are calculated at Decimal precision 65, then rounded to rational multiples of `10^(-30)`. Here is an explicit error audit for those evaluations. The integral in (17) uses the primitives

```
A_b(y)=2y-b exp(y/b)+1_{y>=b}(y-b)exp(y/b-1),
B_b(y1)-B_b(y0)
 = log(y1/y0)-[S(y1/b)-S(y0/b)]
   +1_{y1>=b}(exp(y1/b-1)-1)
   -1_{y0>=b}(exp(y0/b-1)-1),
S(u)=sum_{k>=1} u^k/(k k!).
```

Only `u<=3/2` occurs in S. Truncation after 48 terms has the rigorous error

```
2*(3/2)^49/(49*49!) < 10^(-53).
```

All intermediate magnitudes are bounded, with fewer than 1000 elementary operations per node. Correctly rounded Decimal `exp` and `ln` at precision 65 and this tail bound put the unrounded node error below `10^(-48)`; after rational rounding it is below `10^(-29)`. The generously enlarged `10^(-25)` allowance in the final integral dominates the resulting error. Branch locations are exact rational grid points, so rounding cannot misidentify a jump.

If the two endpoint values on a cell of width h are `(f0,f1)` and `(g0,g1)`, its internal ordering integral is exactly

```
h^2 (f0*g1-f1*g0)/6.
```

Different-cell contributions are just products of cell integrals. All rational-node contributions are accumulated as a single integer. The resulting rational `B_linear` is

```
 404251705523702555276579835049671986804777496216571128401392761786
 / (12 * 30000^2 * 10^60).
```

It is approximately `0.00003743071347441690326635`. The script verifies, by exact rational comparisons,

```
37/10^6 < B_linear - 1/4050000 - 10^(-25),
B_linear + 1/4050000 + 10^(-25) < 38/10^6.
```

The more precise endpoints in (19) come from the same rational certificate. The recorded run passed all checks; see `FullPartitionVerification.log`.

## 6. A small, literal deterministic countermodel

For an entirely finite exact check, use these five partitions, with every displayed part divided by 4:

```
A=(1,1,1,1), B=(1,1,2), C=(1,3), D=(2,2), E=(4).
```

Their uniform-permutation/Ewens(1) weights are `(1,6,8,3,6)/24`. Take the following **integer transition counts**:

```
       A   B   C   D   E
 A     1   7   6   2   8
 B     5  36  52  21  30
 C    10  44  64  22  52
 D     4  15  26   9  18
 E     4  42  44  18  36.
```

Rows and columns have the same sums, `(24,144,192,72,144)`. The graph is connected, so a deterministic Euler tour using the least available next vertex produces a periodic word with exactly these 576 adjacent-pair counts.

For every two integer subpartitions alpha,beta with combined weight at most 4, this word has

```
mean [ prod_k (C_k(A_n))_{m_k(alpha)}
       prod_k (C_k(A_{n+1}))_{m_k(beta)} ]
 = prod_k k^(-m_k(alpha)-m_k(beta)).                     (24)
```

Here `(z)_m` is a falling factorial and C_k counts parts k/4. Thus every discretized factorial correlation through combined mass 1 is exactly that of two independent uniform-permutation partitions, as are the complete marginals. All mass-conservation identities hold pointwise.

But the sum of `sgn(max A_(n+1)-max A_n)` over the period is 8, giving mean `1/72`. The script checks all 38 admissible selector pairs, not just first moments, and independently constructs and verifies the Euler tour.

This finite example alone would not settle the PD issue, due to its atoms and ties. Sections 2–5 specifically remove that weakness.

### Determinizing the PD countermodel, if a sequence rather than a law is wanted

Equation (11) specifies all weights explicitly; no weights are chosen randomly. It also admits a literal deterministic sequence realization. Quantize the partition space on successively finer rational grids and approximate the resulting balanced edge-flow matrices of Q by rational balanced positive matrices. This is possible because row and column measures agree. Choose the first rational matrix in a fixed enumeration satisfying each specified rational error tolerance, and use its least-next-vertex Euler tour. Mass-one representatives of the cells can be used. Repeat and concatenate the tours, increasing accuracies and ensuring that each new tour length is negligible compared with the accumulated earlier repetitions. The resulting deterministic sequence has adjacent empirical law Q. A countable determining class of factorial tests supported away from zero, and the zero-mass tie boundary, give (2) and (22) along this sequence.

This is an abstract partition sequence, not a sequence of prime factorizations of consecutive integers. The finite table above avoids any generic-point argument if only the finite algebraic obstruction is needed.

There is also no need to postulate the biased law at every scale. At the level of abstract partition sequences, use biased Q blocks only on `[N_j,2N_j)`, with `N_j=2^(2^j)`, and symmetric blocks elsewhere, choosing the Euler approximations sufficiently fine and their periods negligible compared with the block lengths. Both block laws have the same specified marginal and subcritical data. The biased blocks have logarithmic weight only `O(j)` up to `2N_j`, compared with `log N_j` of order `2^j`; the logarithmic ordering mean is therefore zero. The ordinary ordering mean remains biased along `2N_j`. Outside `[N_j,jN_j]` its bias tends to zero, and the exceptional scales have logarithmic density zero. This observation concerns compatibility of the abstract data, not cross-scale arithmetic consistency of actual factorizations.

## 7. Where the favorable complementary-cofactor observation stops

For large exponents `alpha<beta`, both above 1/2,

```
alpha + (1-beta) < 1.
```

So a prime p on the smaller-largest-factor side and the **complete** complementary cofactor b on the other side have a subcritical product. The arithmetic observation is correct.

But `b|n+1` is not the assertion that `(n+1)/b` is a prime larger than p. The latter is a condition on the **unselected residual partition**. A factorial selection statistic counts b also when further unselected factors remain. Specifying that an observed collection is the complete cofactor, rather than merely part of it, requires a stopping/absence test. Its expectation is not supplied by (2).

The countermodel makes this failure quantitative: all selected-factor statistics through mass 21/20 have exactly their independent values, yet the ordering current changes by a fixed amount. In a joint size-biased recursion, substituting the one-partition residual PD law *conditionally on the other partition* would discard (12). The marginal deletion identity is true; that conditional substitution is not.

The exact signed modes satisfy the full deletion/mass equations (14), so repeatedly applying those equations does not force them to shrink to zero. A proposed contraction that does shrink them must be using something beyond the stated conservation and subcritical data.

## 8. What is ruled out, and what is still open

Let V be the span of:

* arbitrary one-partition observables;
* mixed factorial observables supported in `s+t<1` (even `<=21/20` here);
* universal identities obtained from exact mass conservation.

Q and `mu x mu` have identical expectations on V, but not on the winner statistic W. Therefore W cannot be recovered in an L1-controlled way from V. For example, if `v_j` have zero independent-law mean and are such linear combinations, then

```
||W-v_j||_(L1(Q)) >= |E_Q W| > 10^(-5).
```

Since `dQ/d(mu x mu)<=3/2`, even an `L1(mu x mu)` approximation would have error bounded below by `(2/3)*10^(-5)`. Thus a uniformly integrable infinite linearization cannot hide the obstruction in a vanishing tail.

This does **not** say that antisymmetric cancellation requires full joint independence. It says that the full partition conservation hierarchy and all the stated subcritical limiting CRT data still leave an antisymmetric mode detected by the winner. Arithmetic signed progression estimates, genuinely new conditional information on residual prime factors, or quantitative estimates beyond these limiting data could exclude the mode. None is supplied by the mass-conservation argument alone.

In particular no `o(X)` error for the actual integers has been proved in this attempt. The new outcome is the explicit full-PD, all-order countermodel and its quantitative no-linearization obstruction.
