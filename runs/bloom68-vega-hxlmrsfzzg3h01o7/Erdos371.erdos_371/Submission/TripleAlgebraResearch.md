# Erdős 371: triple algebra and a positive-density polynomial matching obstruction

## Outcome and scope

This is an unconditional deduction about the **actual** largest-prime-factor function. It does **not** prove natural density 1/2, and does not claim the signed bypass estimate. No specification file is imported, used as a theorem, or edited.

The principal deductions are:

1. **Strongest result, Section 7:** an explicit set of upper bypasses has positive lower natural density and label product greater than `(n+1)^(41/20)`. Every sign-reversing mate that preserves the **unordered set of all three LPF labels**, allowing arbitrary permutations, satisfies `m>(n+1)^(21/20)/6`. Hence at most `O_C(X^(20/21))` of these sources can be paired inside `[1,CX]`. This gives a linear obstruction to a natural-prefix almost-permutation by any abc label permutation.
2. A larger specified set of lower bypasses has **positive lower natural density**, with lower logarithmic density at least `(1-log 2)(2 log 2-1) = 0.1185355138...`. On active triples, a swap of the first two largest factors retaining the third has the universal prime-triple counting bound (16).
3. Both positive-density deductions use one-point smoothness and an established **binary**, fixed-shift logarithmic-window theorem. The fixed-parity form needed in Section 7 is proved directly using the principal character modulo 2; it is not inferred from an average. No three-point distribution is assumed.
4. The six projective abc permutations and positive Stern–Brocot moves have exact no-return statements for the consecutive slice. A support-preserving endpoint-swap lift has an almost-everywhere **cubic** escape barrier; other support permutations face a quadratic one.

These are obstructions to label-preserving algebraic implementations, not a theorem excluding a bijection that introduces different prime labels, a nonlocal signed argument, or all conceivable uses of S-unit equations.

## 1. Exact signed residual; logarithmic cancellation is automatic

Put `P(1)=1`,

\[
x_n=P(n),\quad y_n=P(n+1),\quad z_n=P(2n+1),\qquad
r_n=s_n(1-B_n).
\]

For `n>=1`, the supplied exact identity gives

\[
r_n=s_n-\tfrac12(s_{2n}+s_{2n+1}).                         \tag{1}
\]

If `S(X)=sum_{1<=n<=X}s_n` and `R(X)=sum_{1<=n<=X}r_n`, with integer X, then

\[
2R(X)=2S(X)-S(2X+1)+1.                                    \tag{2}
\]

In particular, the sought estimate remains `R(X)=o(X)`, equivalently ordinary dyadic flatness. Nothing below asserts it.

There is an important exact warning about logarithmic tests. For integers `U>=L>=2`, (1) implies

\[
\sum_{L\le n\le U}\frac{r_n}{n}
=\sum_{L\le n\le U}\frac{s_n}{n}
 -\sum_{2L\le m\le2U+1}\frac{s_m}{m}
 -\sum_{L\le n\le U}\frac{s_{2n+1}}{2n(2n+1)}.              \tag{3}
\]

The two large sums cancel except at the end intervals. Thus the absolute value of (3) is at most `2 log 2 + O(1/L)`, uniformly in U. Vanishing residual averages on growing logarithmic windows are therefore **automatic for this dyadic coboundary**, even without information about P. They do not prove the ordinary estimate (2).

## 2. Substantial mass on active lower bypasses

Define the fixed set

\[
\mathcal V=\{n\ge2:\ x_n^2>n+1,\ y_n^2>n+1,\ z_n^2\le n+1\}.
                                                               \tag{4}
\]

Every member has `z_n<min(x_n,y_n)`, so `|r_n|=1`. Moreover,

\[
x_ny_n>n+1,\qquad x_ny_nz_n>n+1.                            \tag{5}
\]

### 2.1 The only non-elementary analytic input

Let

\[
f(m)=1_{P(m)\le\sqrt m},\qquad d=\rho(2)=1-\log2.
\]

The binary smoothness theorem in its **logarithmic-window** form says that, for every function `omega(T)->infinity` with `1<=omega(T)<=log(3T)`,

\[
\frac1{\log\omega(T)}
\sum_{T/\omega(T)<m\le T}\frac{f(m)f(m+1)}m
\longrightarrow d^2.                                      \tag{6}
\]

This is the fixed shift 1 theorem, not a conclusion drawn from averaging shifts. A source checked directly is Teräväinen, *On binary correlations of multiplicative functions*, arXiv:1710.01195: `theo_bincorr` (lines 54–58 of the local source), equation `eqq79` (lines 748–750, with k=l=0), and the application with arbitrary omega in the proof of `theo_hildebrand`, lines 782–796. The globally logarithmic version is `theo_density`, lines 134–138. Changing the second cutoff from `sqrt(m)` to `sqrt(m+1)` affects only possible prime-square endpoints and is harmless in these windows. The arbitrary-slow-window quantifier in (6) is essential below.

The one-point natural density of f is d. At exponent 1/2 this also follows directly by counting the unique prime `p>sqrt(m)` dividing m and using the prime reciprocal sum. Multiplication by 2 changes f only on `O(T/log T)` indices up to T: for `n` in a dyadic interval, a discrepancy requires a prime factor in a fixed-ratio interval around `sqrt(n)`. Counting its multiples proves the bound. Hence

\[
\sum_{n\le T} f(2n+1)=dT+o(T).                              \tag{7}
\]

### 2.2 Exact inclusion–exclusion after doubling

Set

\[
v'_n=(1-f(2n))f(2n+1)(1-f(2n+2)),\quad
A(m)=f(m)f(m+1),\quad
J_n=f(2n)f(2n+1)f(2n+2).
\]

The following is an exact Boolean identity:

\[
v'_n=f(2n+1)-A(2n)-A(2n+1)+J_n.                            \tag{8}
\]

In a logarithmic n-window, the sum of the two A terms is **exactly the combined even and odd adjacent-pair sum**, up to a summable weight correction:

\[
\sum_{L\le n\le U}\frac{A(2n)+A(2n+1)}n
=2\sum_{2L\le m\le2U+1}\frac{A(m)}m
 +\sum_{L\le n\le U}\frac{A(2n+1)}{n(2n+1)}.                \tag{9}
\]

No distribution in either parity class separately is needed. Apply (6) at the doubled window, use (7), and discard `J_n>=0`. This gives, for every allowed omega,

\[
\liminf_{T\to\infty}
\frac1{\log\omega(T)}
\sum_{T/\omega(T)<n\le T}\frac{v'_n}{n}
\ge d-2d^2.                                                \tag{10}
\]

When applying (6) at `2T`, use the allowed function `omega_2(t)=omega(t/2)`; endpoint changes cost `o(log omega(T))`.

Let `v_n=1_{n in V}`. For `n>=2`, exact preservation `P(2n)=P(n)` shows that `v_n` and `v'_n` can differ only when, for one of `j=0,1,2`,

\[
n+1<P(2n+j)^2\le2n+j.
\]

For `T<=n<=2T` the responsible prime lies between fixed multiples of `sqrt T`. Counting its multiples in the corresponding linear form gives `O(T/log T)` discrepancies. Consequently this change has normalized logarithmic-window error `o(1)` for every omega in (6). Therefore

\[
\boxed{\quad
\liminf_{T\to\infty}
\frac1{\log\omega(T)}
\sum_{T/\omega(T)<n\le T\atop n\in\mathcal V}\frac1n
\ge c_0:=(1-\log2)(2\log2-1)>0.
\quad}                                                     \tag{11}
\]

The globally logarithmic version of the same proof gives

\[
\underline\delta_{\log}(\mathcal V)\ge c_0
=0.1185355138434330789\ldots.                               \tag{12}
\]

There is no assertion that the three-point logarithmic density exists.

### 2.3 Why positive lower **natural** density really follows here

Write `V(T)=#(V cap [1,T])`. This passage does not use (12) alone.

Suppose `liminf V(T)/T=0`. Choose `T_j` increasing sufficiently quickly that

\[
V(T_j)/T_j\le j^{-3},\qquad j\le\log(3T_j).
\]

Choose one allowed, stepwise increasing function omega with `omega(T_j)=j` (set it equal to j on `[T_j,T_{j+1})`). Then

\[
\sum_{T_j/j<n\le T_j\atop n\in\mathcal V}\frac1n
\le\frac j{T_j}V(T_j)\le j^{-2},
\]

contradicting (11), whose lower bound is eventually `(c_0/2) log j` along this same sequence. Thus

\[
\boxed{\ \underline d(\mathcal V)>0.\ }                    \tag{13}
\]

The positive constant in (13) is **not** claimed to be c_0, and no effective numerical value is provided. The global logarithmic bound also implies `limsup V(T)/T>=c_0`. Positivity (13) relies on both nonnegativity and the every-omega quantifier; it cannot be copied to infer a natural mean of zero for the signed residual in (3).

## 3. A universal triple-label escape theorem

For `n>=2` let

\[
p=P(n),\quad q=P(n+1),\quad r=P(2n+1),\quad M=pqr.
\]

These are distinct primes and r is odd. Call n **active** if `M>n+1`.

Suppose a positive integer m has the reversed triple labels

\[
P(m)=q,\qquad P(m+1)=p,\qquad P(2m+1)=r.                   \tag{14}
\]

Then

\[
p\mid n+m+1,\quad q\mid n+m+1,\quad r\mid2(n+m+1).
\]

Since r is odd and the primes are distinct,

\[
\boxed{\ M\mid n+m+1.\ }                                  \tag{15}
\]

The label equalities (14) imply `r_m=-r_n`. The divisibility condition (15) is necessary; it is emphatically **not sufficient** for preservation of largest prime factors.

Let `Pi_3(T)` count squarefree integers at most T with exactly three prime factors. Uniformly for `X,Y>=2`,

\[
\boxed{
\#\{n\le X:M(n)>n+1,\ \exists m\le Y\text{ satisfying (14)}\}
\le6\Pi_3(X+Y+1)
\ll\frac{(X+Y)(\log\log(X+Y))^2}{\log(X+Y)}.
}                                                         \tag{16}
\]

**Proof.** Equation (15) gives `M<=X+Y+1`. For an ordered triple `(p,q,r)`, the congruences

\[
n\equiv0\pmod p,\quad n\equiv-1\pmod q,\quad
2n\equiv-1\pmod r
\]

determine one residue modulo M. Activity gives `0<n<M`, so at most one source n. Each squarefree product has at most six ordered assignments. For the elementary upper bound, sort the primes `a<=b<=c`; then `ab<=T^(2/3)`, and the prime-counting upper bound gives

\[
\Pi_3(T)\ll\frac T{\log T}
\sum_{a\le T^{1/3}\atop a\text{ prime}}\frac1a
\sum_{b\le\sqrt{T/a}\atop b\text{ prime}}\frac1b
\ll\frac{T(\log\log T)^2}{\log T}.
\]

In particular, the left side of (16) is `o(X)` for `Y=CX`, any fixed C. It remains `o(X)` for `Y=X L(X)` when `L>=1` and `L=o(log X/(log log X)^2)`.

### Actual linear obstruction, not just a formal CRT difficulty

Every n in V is an active nonzero bypass. By (13), there is `c_*>0` such that, for all sufficiently large X, `V(X)>=c_* X`. Hence any map satisfying (14) on these sources has

\[
\#\{n\in\mathcal V,\ n\le X:\ m(n)>CX\}
\ge c_*X-o(X).                                             \tag{17}
\]

No choice of mate, iteration count, injectivity convention, or bounded distortion of the prefix can evade this necessary-condition bound while keeping the final labels (14). In measure terms, if `mu_X` is unit counting measure on these sources and `F_X` is such a map, then

\[
\tfrac12\|(F_X)_*\mu_X-\mu_X\|_1\ge c_*X-o(X).              \tag{18}
\]

Test on `[1,CX]` for `C>=1`. Altering source weights by `o(X)` in l1 does not fix the loss. An argument allowing the endpoint prime labels to change is outside this theorem's scope.

## 4. What the abc and S-unit symmetries actually do

Use the primitive signed zero-sum triple

\[
(A,B,C)=(n,n+1,-2n-1),\qquad A+B+C=0.
\]

For a permutation `(A',B',C')`, normalize the difference of the first two terms to 1. The new parameter is `A'/(B'-A')`. The six resulting rational maps are exactly

\[
n,\quad -n-1,\quad
-\frac n{3n+1},\quad -\frac{n+1}{3n+2},\quad
-\frac{2n+1}{3n+1},\quad -\frac{2n+1}{3n+2}.                 \tag{19}
\]

For positive n, only the identity has a positive integral value. The reflection `-n-1` is an integer but is negative; it reverses the residual when P is extended using absolute values. The other four fractions are reduced, nonintegral, and negative. Thus the actual abc permutation orbit supplies no other point of the positive consecutive slice.

This is also immediate from primitiveness: rescaling a permuted integer triple to another primitive integer triple allows only common scale `+1` or `-1`. The other differences have absolute values `3n+1` or `3n+2`, not 1. Clearing those new denominators introduces different linear forms; it is not an invariance of the original three prime-factor labels.

### A precise distinction for changed-third-label transports

One can instead ask only for **permuted prime-label divisibility**, not an actual permutation of the three numerical terms. For a map in (19), initially take `N=A'` and `D=B'-A'` (changing both signs later does not affect divisibility). If m realizes its corresponding label permutation, then

\[
M\mid D(n)m-N(n).
\]

To see this, the three identities `D L_i(m)-L_{pi(i)}(n)=a_i(Dm-N)` have `a_i=1,1,-2`; the prime assigned to the odd third form must be odd. The four nonaffine maps consequently give, respectively,

\[
M\mid(3n+1)m+n,\quad M\mid(3n+2)m+n+1,
\]
\[
M\mid(3n+1)m+2n+1,\quad M\mid(3n+2)m+2n+1.
\]

These are **quadratic-size** constraints for `n,m` in comparable positive intervals, unlike the linear-size constraint (15). Thus (16) must not be asserted for these changed-third-label transports: merely bounding their moduli by `O(XY)` gives no useful `o(X)` count when `Y` is comparable with X. Thus (16) alone does not exclude this route. Section 7 supplies the extra positive-density, superquadratic-product input that obstructs these permutations too. For full termwise prime supports, the radical argument below already forces `m>=X^(2-epsilon)` for almost all sources under any of these nonaffine permutations.

### Positive Stern–Brocot no-return

If `U` is a nonnegative integral 2-by-2 matrix with determinant `+1` or `-1`, other than identity or the swap matrix, then for `a,b>=2` the two coordinates of `U(a,b)` differ by at least `min(a,b)`.

Indeed, if its rows are componentwise comparable, this is immediate. If they strictly cross, write one row `(u,v)` and the other `(w,t)` with `u>w` and `v<t`. Then

\[
ut-vw=(u-w)t+w(t-v)\ge t+w.
\]

A determinant of magnitude 1 forces the identity matrix; reversed crossing forces the swap. Therefore positive mediant/addition words cannot carry `(n,n+1)`, `n>=2`, to a different consecutive pair. Subtractive/unrestricted modular words are not ruled out, but they are no longer this positive, label-preserving construction.

### Support-preserving lifts face a cubic barrier

If a positive lift swaps the complete prime supports of n and n+1 and retains that of `2n+1` (even retaining the original supports as inclusions suffices), then

\[
\operatorname{rad}(n(n+1)(2n+1))\mid n+m+1.                  \tag{20}
\]

For every fixed `epsilon>0`, outside `o(X)` sources `n<=X`,

\[
\operatorname{rad}(n(n+1)(2n+1))\ge X^{3-\epsilon},
\]

with an arbitrarily small adjustment of epsilon if a factor 2 is wanted. Indeed

\[
\sum_{k\le2X+1}\log\frac{k}{\operatorname{rad}k}
\le(2X+1)\sum_p\frac{\log p}{p(p-1)}\ll X.
\]

Apply Markov to the three terms and discard `n<=X^(1-epsilon/6)`. Consequently every such lift has `m>=X^(3-epsilon)` for all but `o(X)` sources, after adjusting epsilon. No abc conjecture is used. This concerns preservation of the termwise supports, not arbitrary operations inside a fixed global S-unit group.

## 5. Positive triple reflection fails even pointwise for actual P

Write

\[
n=pa,\qquad n+1=qb,\qquad2n+1=rc,
\quad qb-pa=1,\quad pa+qb=rc.
\]

The least positive reflected residue, when n is active, is `m=M-n-1`. Its factors are

\[
m=q(pr-b),\quad m+1=p(qr-a),\quad2m+1=r(2pq-c).              \tag{21}
\]

The sum relation survives exactly, but the required complementary smoothness does not. To obtain (14), one would need

\[
P(pr-b)\le q,\quad P(qr-a)\le p,\quad P(2pq-c)\le r.         \tag{22}
\]

These do not follow from the original cofactor smoothness conditions. For example `n=2` has labels `(2,3,5)` and `M=30`, whereas `m=27` has labels `(3,7,11)`. The reflection does not even reverse the ordering sign in this example. A claimed triple involution based only on retaining divisibility would therefore be false.

Actual successful nonlocal mates also exist; the obstruction is not a claim of absolute nonexistence. For example, `n=8342` belongs to V and has labels `(97,103,71)`, while `m=701018` has labels `(103,97,71)`. Here `97*103*71=n+m+1=709361`. The relevant factorizations are

```
8342    = 2*43*97,       8343    = 3^4*103,
16685   = 5*47*71,
701018  = 2*41*83*103,   701019  = 3^2*11*73*97,
1402037 = 7^2*13*31*71.
```

The lower prime supports change, and the mate lies far outside the source's scale.

## 6. The remaining incomplete triple-fiber current

Here is an explicit version of the analytic gap, retaining all three cofactor conditions.

For primes `p<q` and an odd prime `r` outside `[p,q]`, set `M=pqr`. Let `t=t(p,q,r)` be the unique residue in `[0,M)` with

\[
p\mid t,\quad q\mid t+1,\quad r\mid2t+1.
\]

In fact `1<t<M-1`, and the reversed residue is `t^-=M-1-t`. Put

\[
H^+=1_{P(t/p)\le p}\,1_{P((t+1)/q)\le q}\,
       1_{P((2t+1)/r)\le r},
\]

\[
H^-=1_{P(t^-/q)\le q}\,1_{P((t^-+1)/p)\le p}\,
       1_{P((2t^-+1)/r)\le r}.
\]

The active signed bypass sum, excluding the harmless n=1 endpoint, is exactly

\[
R_{\rm act}(X)
=\sum_{p<q,\ r\notin[p,q]}
 \left(H^+1_{t\le X}-H^-1_{M-1-t\le X}\right).               \tag{23}
\]

The sum is effectively finite. Inactive occurrences lie in the later periods `t+kM`, `k>=1`, and are **not** being discarded:

\[
R(X)=O(1)+R_{\rm act}(X)
 +\sum_{n\le X\atop M(n)\le n+1}r_n.                       \tag{24}
\]

The abc relation produces the complementary residues and (21), but gives neither equality of `H^+` and `H^-` nor cancellation of the two cutoff indicators. Even imposing `H^+=H^-` would not give a natural-prefix pairing: (16)–(18) show a linear obstruction on actual nonzero residuals. A natural-prefix bijection must therefore abandon the swap-and-retain-third rule on linearly many bypasses. A nonlocal or genuinely relabelling approach is not excluded; the changed-third-label bilinear constraints above identify one distinction that matters. No aggregate signed cancellation of (23) together with the inactive term in (24), or any other proof of `R(X)=o(X)`, is established here.

## 7. Stronger extension: polynomial escape for **every** three-label permutation

The bilinear constraints in Section 4 have a useful consequence once one constructs non-negligible bypass mass with `M>n^(2+eta)`. This can also be done with binary input only. The needed parity conditioning is obtained **directly from the theorem**, not inferred from an unconditioned average.

### 7.1 A direct fixed-parity binary lemma

Write `F_u(m)=1_{P(m)<=m^u}` and `delta_u=rho(1/u)`. For fixed `u,v` in `(0,1)`, every allowed omega, and either `epsilon=0` or `epsilon=1`,

\[
\frac1{\log\omega(T)}
\sum_{T/\omega(T)<m\le T\atop m\equiv\epsilon\pmod2}
\frac{F_u(m)F_v(m+1)}m
\longrightarrow\tfrac12\delta_u\delta_v.                  \tag{25}
\]

Here is why (25) is available without assuming a progression version of an unweighted theorem. Freeze the cutoffs at `T^u,T^v`, writing the resulting completely multiplicative functions as `g_u,g_v`. Let `chi_0(m)=1_{m odd}`, the principal character modulo 2. Then

\[
1_{m\equiv0\pmod2}\,g_u(m)g_v(m+1)
=g_u(m)\,(g_v\chi_0)(m+1).
\]

Apply Teräväinen's `theo_bincorr` with shift **1**, uniform factor `g_1=g_u`, and multiplicative real factor `g_2=g_v chi_0`. Only the first factor is required to satisfy the uniformity hypothesis. Their interval means are `delta_u+o(1)` and `delta_v/2+o(1)`, respectively; the latter is the ordinary odd smooth-number marginal. This proves the even case. Subtract it from the unconditioned binary formula to obtain the odd case.

Unfreezing the cutoffs is legitimate uniformly for every allowed omega. A discrepancy for `F_u` requires a prime in `[(T/omega(T))^u,T^u]`. Summing harmonic weights of its multiples bounds the normalized error by

\[
O_u\!\left(\frac{1+\log\omega(T)}{\log T}\right)+o(1)=o(1).
\]

Multiplication by `chi_0` cannot enlarge this error. Thus (25) is a direct application of the same main theorem and the one-point fixed-progression smoothness estimate (`eqq90`, source lines 666–669), not an inference of conditional independence from an average. Finite linear combinations give (25) for exponent intervals and their complements as well.

### 7.2 A positive-lower-density high-bypass set with superquadratic label product

Choose

\[
a=19/20,\qquad b=11/20,
\]

and define the fixed set

\[
\mathcal H=\{n\ge2:\ (n+1)^b<x_n,y_n\le(n+1)^a<z_n\}.
                                                               \tag{26}
\]

Set `E=F_a-F_b`, `H=1-F_a`, `G=1-E`. Their one-point means are

\[
e=\log(a/b)=\log(19/11),\qquad h=-\log a=\log(20/19).
\]

Outside `O(T/log T)` indices up to T, the indicator of (26) equals

\[
w_n=E(2n)H(2n+1)E(2n+2).
\]

This follows from exact doubling and fixed-ratio prime-factor cutoff bands, exactly as in Section 2, now at the two fixed exponents a and b. Pointwise,

\[
w_n\ge H(2n+1)-G(2n)H(2n+1)-H(2n+1)G(2n+2).
\]

The middle marginal has mean h. After the exact change from n to `2n` or `2n+1`, (25) makes **each** subtracted term have logarithmic-window mean `h(1-e)`. Therefore, for every allowed omega,

\[
\boxed{
\liminf_{T\to\infty}\frac1{\log\omega(T)}
\sum_{T/\omega(T)<n\le T\atop n\in\mathcal H}\frac1n
\ge\kappa:=\log(20/19)\bigl(2\log(19/11)-1\bigr)
=0.00477476006525024\ldots>0.
}                                                         \tag{27}
\]

Positivity here is elementary, not based on the displayed decimal: `log(19/11)>8/15` and `log(20/19)>2/39` follow from `log t >= 2(t-1)/(t+1)` for `t>=1`. In particular `kappa>2/585>0`.

The nonnegative arbitrary-slow-window argument of Section 2.3 now proves

\[
\boxed{\ \underline d(\mathcal H)>0.\ }
\]

Stitching the windows also gives lower logarithmic density at least kappa. Neither existence of the natural density nor a natural lower bound equal to kappa is asserted.

Every `n in H` is an actual **upper bypass**, and

\[
|r_n|=1,\qquad M(n)>(n+1)^{2b+a}=(n+1)^{41/20}.            \tag{28}
\]

This is the ingredient that makes the bilinear, rather than merely linear, congruences obstruct a natural-prefix matching.

### 7.3 Universal polynomial escape for label-set-preserving sign reversal

Suppose `n in H` and a positive m satisfies

\[
\{P(m),P(m+1),P(2m+1)\}=\{x_n,y_n,z_n\},\qquad r_m=-r_n.
\]

The labels are distinct, so they specify one of the six permutations. The identity permutation cannot reverse a nonzero residual. For each of the other five permutations, its rational map in (19) is negative at positive n. Consequently `D(n)m-N(n)` is a **nonzero** multiple of M. The bounds on N and D in (19) give

\[
M\le |D(n)m-N(n)|\le(3n+2)m+2n+1.                          \tag{29}
\]

For `n>=3`, combine (28) with (29) to obtain

\[
\boxed{\ m>\frac{(n+1)^{21/20}}6.\ }                      \tag{30}
\]

Indeed `(n+1)^(41/20)>=4n+2` and `3n+2<=3(n+1)`. The finitely many smaller indices are irrelevant. On a bypass triple, `r=sgn((y-x)(z-x)(z-y))`, so sign reversal actually requires an odd permutation; bounding all five nonidentity maps merely avoids an unnecessary case distinction.

In particular, uniformly for `X,Y>=2`,

\[
\#\{n\in\mathcal H\cap[1,X]:\ \exists m\le Y
\text{ with the same unordered triple and }r_m=-r_n\}
\le (6Y)^{20/21}+O(1).                                    \tag{31}
\]

For `Y=CX`, this is `O_C(X^(20/21))=o(X)`. Since H has positive lower natural density, **every** attempt to reverse residuals by merely permuting their three largest-prime-factor labels has a linear natural-prefix loss. Allowing the third label to move does not fix it. The obstruction even persists inside `[1,X^(1+delta)]` for each fixed `delta<1/20`.

More generally, the same construction works whenever

\[
1/2<b<a<1,\qquad \log(a/b)>1/2,\qquad 2b+a\ge2+\eta.
\]

It provides a positive-lower-density set of bypasses whose label-set-preserving reversing mates satisfy `m>>n^(1+eta)`. Such choices exist for every

\[
0<\eta<2\exp(-1/2)-1=0.2130613\ldots.
\]

This is a range delivered by this construction, not a claim of an optimal obstruction exponent.

### Scope of the strengthened conclusion

A near-local natural-prefix bijection cannot be built from **any permutation of the three LPF labels** on all but `o(X)` bypasses: on a positive-density subset it must introduce a different largest prime factor, not simply move the old third label. General relabelling, nonlocal signed cancellation, and other analytic proofs remain possible. Neither (27) nor (31) proves `R(X)=o(X)`; they provide a triple-specific obstruction to the proposed symmetry mechanism.

## Verification

`TripleAlgebraVerification.py` checks exact doubling and signed sums, Boolean identities, rational logarithmic-weight corrections, the lower-bypass/activity implications, the CRT residue and complement formulas, actual reversed-label matches, the six projective maps, and nonnegative unimodular no-return cases. The extension also checks exact integer-power membership of the high-bypass set, all-permutation polynomial escape, and multiplicativity of the parity projector used in (25). These are checks of the finite algebra, not numerical proofs of the analytic inputs or asymptotic conclusions. No Lean formalization of the new analytic deductions is claimed.

The recorded run passed one million dyadic and lower-bypass checks, 302,610 polynomial-escape checks on 60,522 exactly counted high bypasses up to one million, 39,000 parity/multiplicativity checks, 2,548 ordered-triple CRT checks, and 14,560 all-permutation divisibility checks. Five active-fiber currents were independently counted. Both successful nonlocal mates and a failed naive reflection were checked. The output is in `TripleAlgebraVerification.log`; finite counts are not used as evidence of limiting densities.

The reference input (6) was checked in the local arXiv source; importantly, its arbitrary-omega version rather than only its global logarithmic corollary is used for (13) and (27). For (25), the main theorem's requirement of uniformity on only the first factor, and the one-point progression input `eqq90`, were checked directly.

`Submission/Spec.lean` remains unchanged, with SHA-256 `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
