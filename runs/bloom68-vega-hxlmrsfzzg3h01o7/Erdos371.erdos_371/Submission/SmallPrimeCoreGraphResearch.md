# Small-prime-core graphs: a fixed-scale obstruction, including coordinate SI/AP uniformity

## Result and scope

**The proposed label-uniform cut estimate is false.** This note gives analytic counterexamples on the actual small-prime-core graph, for every finite prime cutoff, with a lower bound independent of that cutoff. They are not simulated graphs and do not use a conjecture about primes.

Write `c_K(n)=core_K(n)`, and let `R_K` be the positive integers having no prime factor at most `K` (including 1). For real labels on `R_K`, put

\[
 J_K(X;a,b)=\frac1X\sum_{n=1}^X
 [a(c_K(n))b(c_K(n+1))-b(c_K(n))a(c_K(n+1))].                 \tag{1}
\]

Here and below `X` is an integer unless a floor is displayed. The following statements are proved.

1. For **every fixed finite** `K>=2`,
   \[
   \liminf_{X\to\infty}\ \sup_{|a|,|b|\leq1}J_K(X;a,b)
       \ \geq\ I(1/2)\ \geq\frac7{64},
   \qquad I(c)=\int_0^1\sin(c/u)\,du.                       \tag{2}
   \]
   The labels inside this supremum may depend on `X`, as a uniform cut estimate must allow. For labels in `[0,1]`, and even for a supremum over two indicator labels, the lower bound is `7/256`.
2. There is also, for **each** fixed `K`, **one fixed pair** `a_K,b_K` on all of `R_K`, independent of the counting scale, such that
   \[
   \limsup_X J_K(X;a_K,b_K)\geq I(1/2).                     \tag{3}
   \]
   Its lifted label `z(n)=a_K(c_K(n))+i b_K(c_K(n))` has the uniform-circle marginal in every fixed progression, at all scales. Every continuous mean-zero function of `z` satisfies the all-scale, averaged-over-starting-points short-interval mean-square assertion, also in every fixed progression. Precise quantifiers and a proof are in section 4.
3. Thus **adding the known type of coordinate SI/AP mean-zero assumptions does not repair a bound uniform over core labels**. This conclusion holds for fixed label functions, not merely a triangular array. If a scalar label with the Dickman marginal is desired, the fixed example can be mapped to that marginal while retaining these coordinate properties and the nonzero antisymmetric product test.
4. The obstruction survives removing any set of cores whose **total positional multiplicity** is `o(X)`. It also rules out decay of the multiplicity-normalized skew operator norm. It is not just an exceptional low-degree-vertex obstruction.
5. On the same resonant examples the normalized prime harmonic average of smaller-scale currents can tend to zero as the prime set grows, while (2) stays positive. Section 6 gives the exact scale identity and bound.

**Logical boundary.** These are counterexamples to a generic-label graph estimate, **not to LPF or to its full uniform growing-dilation package**. The quantifiers are `for every finite K there exist labels`; no single nonconstant label is asserted to be exactly invariant under every prime. In particular, this is not the old `K=2` example promoted to all `K`. The counterexamples use all primes at most the chosen, arbitrarily large, finite `K`. They do not prove or disprove the ordinary density of `P(n+1)>P(n)`. No admitted target of `Spec.lean` is used, and no Lean file is changed.

## 1. Core reduction, exceptional sets, and the correct normalization

Let

\[
 S_K=\{\prod_{p\leq K}p^{e_p}:e_p\geq0\},\quad
 s_K(n)=\prod_{p\leq K}p^{v_p(n)},\quad c_K(n)=n/s_K(n),
 \quad \rho_K=\prod_{p\leq K}(1-1/p).
\]

All prime products in this note are over primes. The cutoff `K` is fixed before taking a limit in `X`.

Useful elementary bounds are

\[
 \sum_{s\in S_K}\frac1s=\rho_K^{-1}<\infty,\qquad
 T_K(D):=\sum_{s\in S_K,\ s>D}\frac1s\longrightarrow0,       \tag{4}
\]
\[
 \#\{n\leq Y:s_K(n)>D\}\leq YT_K(D),\qquad
 \sum_{n\leq Y}v_p(n)=\sum_{h\geq1}\lfloor Y/p^h\rfloor
                       \leq\frac{Y}{p-1}.                \tag{5}
\]

The tail estimate follows by writing `n=s m` with its **full** smooth part `s`; discarding the roughness restriction on `m` only enlarges the count. No independence between adjacent smooth parts is assumed. Also

\[
 \Psi_K(Y):=\#(S_K\cap[1,Y])=O_K((1+\log Y)^{\pi(K)})=o_K(Y). \tag{6}
\]

Thus core 1, or any fixed finite set of cores, has zero positional density. This is a statement for fixed `K`, not uniform as `K` grows with `Y`.

### 1.1 The actual LPF reduction is valid

Assign `f(1)=0` (any value in `[0,1]` also works). The uniform stability inequality from `UniformStabilityResearch.md`, applied with base `c_K(n)>=2`, gives

\[
 |f(n)-f(c_K(n))|\leq\frac{\log s_K(n)}{\log n}.
\]

For `n>=epsilon X` with `s_K(n)<=D`, the right side is at most `log D/log(epsilon X)`, and the base is at least 2 once `X` is large. The omitted proportion is at most `epsilon+T_K(D)+O(1/X)`. Hence

\[
 \limsup_X\frac1X\sum_{n\leq X}|f(n)-f(c_K(n))|
       \leq\epsilon+T_K(D).
\]

First take `X->infinity` with `K,D,epsilon` fixed, then `D->infinity`, then `epsilon->0`. This proves the claimed density and `L1` core approximation. For any fixed bounded continuous tests, the adjacent product currents for `f` and for `f o c_K` consequently differ by `o_{X;K}(1)`. The same approximation transfers the coordinate SI/AP assumptions to `f o c_K` for each fixed `K`; restricting an `L1` error to a fixed progression costs only its fixed modulus.

This valid reduction does **not** make the labels arbitrary for purposes of exploiting additional LPF structure. The counterexamples below identify why the subsequent uniform-over-labels assertion cannot be used.

### 1.2 Graph mass is not counting measure on rough cores

Use positions `1,...,X+1`. Let `F(n,m)=1_{c_K(n)=m}`, let `S(n,n+1)=1` for `n<=X`, and set

\[
 C=F^T S F,\quad A=C-C^T,\quad
 D_X=F^T F=\operatorname{diag}(d_X(m)),\quad
 d_X(m)=\Psi_K((X+1)/m).                                  \tag{7}
\]

Only nonempty core classes are included. Then

\[
 XJ_K(X;a,b)=a^T A b,\quad
 B_X=D_X^{-1/2}AD_X^{-1/2}=E^T(S-S^T)E,\quad
 E=F D_X^{-1/2},\quad E^TE=1,\quad \|B_X\|\leq2.           \tag{8}
\]

The exact row balance is

\[
 \sum_v A(m,v)=1_{c_K(1)=m}-1_{c_K(X+1)=m},\qquad
 \sum_v|A(m,v)|\leq2d_X(m).                               \tag{9}
\]

The number of vertices is `rho_K(X+1)+O_K(1)`, by periodicity of roughness, and their total multiplicity is `X+1`. Thus their average multiplicity tends to `rho_K^{-1}`, which grows as `K` grows. This does not imply cancellation.

For a set `E_X` of cores define its positional mass by

\[
 w_X(E_X)=\frac1{X+1}\sum_{m\in E_X}d_X(m).                \tag{10}
\]

Deleting every edge incident to these cores changes (1), for arbitrary labels bounded by 1, by at most `4(X+1)w_X(E_X)/X`: each position touches at most two edges and a summand is at most 2 in absolute value. For the unit-circle labels below the summand is at most 1, so the constant is 2. Small cardinality of `E_X` alone is not the required condition.

## 2. High-frequency characters almost trivial on any finite smooth semigroup

For `t>0` define

\[
 Z_t(m)=e^{it\log m},\qquad a_t(m)=\Re Z_t(m),\quad b_t(m)=\Im Z_t(m),
 \quad \delta_p(t)=\operatorname{dist}(t\log p,2\pi\mathbb Z).
\]

These are legitimate labels on all rough cores, including `Z_t(1)=1`.

### 2.1 A relatively dense recurrence lemma

For any finite list of real frequencies `omega_1,...,omega_r` and any `eta>0`, there is a finite `R(eta,omega)` such that every real interval of length `R` contains a `t` with

\[
 \max_j\operatorname{dist}(t\omega_j,2\pi\mathbb Z)<\eta.   \tag{11}
\]

**Proof.** The closure in the compact torus of `{(t omega_j)_j:t in R}` is compact. Cover it by finitely many `eta`-balls centered at orbit points `(t_i omega_j)_j`. For every `T`, one such point is within `eta` of `(T omega_j)_j`, so `T-t_i` is a return time. All the `t_i` lie in some fixed `[-M,M]`. An interval centered at `T` of length `2M+2` therefore contains a return time. QED.

No rate, prime distribution, or conjectural Diophantine approximation is needed. With `omega_p=log p`, it follows that one can choose, for **every sufficiently large** integer `X`, a frequency `t_X` such that

\[
 t_X/X\longrightarrow1/2,\qquad
 \max_{p\leq K}\delta_p(t_X)\longrightarrow0.             \tag{12}
\]

For clarity about this selection: for each fixed positive `eta`, (11) supplies a return in `[X/2,X/2+eta X]` for all sufficiently large `X`. Take a decreasing sequence of `eta` and increasing thresholds. All thresholds can depend on the fixed `K`.

### 2.2 A finite, degree-correct lifting estimate

The full smooth part gives the pointwise bound

\[
 |Z_t(c_K(n))-Z_t(n)|
 \leq\sum_{p\leq K}v_p(n)\delta_p(t).
\]

For unit complex numbers `z,w`, the real-label skew product is `Im(conj(z)w)`. Changing its two endpoints changes it by at most the sum of their complex displacements. Therefore (5) proves the **finite inequality**

\[
 \left|J_K(X;a_t,b_t)
   -\frac1X\sum_{n=1}^X\sin\bigl(t\log(1+1/n)\bigr)\right|
 \leq\frac{2(X+1)}X\sum_{p\leq K}\frac{\delta_p(t)}{p-1}.   \tag{13}
\]

This accounts for all valuation tails and core 1, with no truncation and no hidden uniformity in `K`.

## 3. A positive fixed-scale current and a genuine cut obstruction

If `t_X/X->c>0`, then

\[
 \frac1X\sum_{n=1}^X\sin\bigl(t_X\log(1+1/n)\bigr)
       \longrightarrow I(c).                            \tag{14}
\]

Indeed, on `n>=epsilon X`, Taylor expansion gives the phase `c/(n/X)+o_epsilon(1)` uniformly, and a Riemann sum applies. The omitted terms and omitted integral have absolute value at most `epsilon` each. Then let `epsilon` tend to zero. There is no assumed limiting value at `u=0`.

The lower bound in (2) has an elementary exact certificate. On `1/4<=u<=1`, the argument `1/(2u)` lies in `[1/2,2]`, where `sin` is at least `sin(1/2)`. Using `sin(1/2)>=1/2-(1/2)^3/6=23/48`,

\[
 I(1/2)\geq-\frac14+\frac34\sin(1/2)
           \geq-\frac14+\frac34\frac{23}{48}=\frac7{64}.  \tag{15}
\]

The comparison of the two endpoint sine values follows, for example, from `pi>3` and the symmetry and monotonicity of sine on `[0,pi]`. Equations (12)--(15) prove (2).

For nonnegative labels set `a'=(1+a)/2`, `b'=(1+b)/2`. Direct expansion gives

\[
 J_K(X;a',b')=\frac14J_K(X;a,b)
 +\frac{(b-a)(c_K(X+1))-(b-a)(c_K(1))}{4X}.               \tag{16}
\]

The last term is `O(1/X)`. Layer-cake integration gives

\[
 J_K(X;a',b')=\int_0^1\int_0^1
       J_K(X;1_{a'>s},1_{b'>t})\,ds\,dt.                \tag{17}
\]

Some two indicator labels therefore have at least that current. In particular, if the skew cut norm means the supremum over two core subsets, its normalized liminf is at least `7/256` for every finite `K`. An estimate

\[
 \sup_{|a|,|b|\leq1}|J_K(X;a,b)|
       \leq\varepsilon(K)+r_K(X),\quad
 \varepsilon(K)\to0,\quad r_K(X)\to0\ (X\to\infty)        \tag{18}
\]

is impossible even with no uniformity required of the rate `r_K` as `K` varies.

There is also an operator obstruction. For these labels `a(m)^2+b(m)^2=1`, so

\[
 \|D_X^{1/2}a\|\,\|D_X^{1/2}b\|
       \leq\tfrac12(X+1),\qquad
 \|B_X\|\geq\frac{2X|J_K(X;a,b)|}{X+1}.                  \tag{19}
\]

Thus `liminf_X ||B_X||>=2I(1/2)>=7/32`. By (10), neither the cut obstruction nor this norm obstruction can be removed by deleting cores of `o(X)` total positional multiplicity. For a trimmed norm use the same restricted vectors; their squared-norm sum is at most `X+1`, and their bilinear current loses only the incident-edge error just estimated.

## 4. One fixed labeling per K, with all-scale coordinate SI and AP mean-zero

This section prevents a possible quantifier objection to the scale-dependent labels in (2).

### 4.1 Construction of the fixed labels

Fix `K`. Start with `B_2>=10`. Recursively choose

\[
 t_j\in[jB_j,(j+1)B_j],\qquad B_{j+1}=2t_j\quad(j\geq2), \tag{20}
\]

so that

\[
 \Delta_j:=\max_{p\leq K}\delta_p(t_j)\longrightarrow0.   \tag{21}
\]

Such choices exist: the interval in (20) has length `B_j->infinity`; by (11) its minimum return error tends to zero, uniformly in the location of the interval. One can take a minimizer of the continuous maximum-distance function on the closed interval. We have

\[
 2j\leq B_{j+1}/B_j\leq2(j+1),\qquad
 t_j\leq(j+1)B_j,\qquad j=O(\log B_j).                  \tag{22}
\]

Define a **single** label on the rough cores by

\[
 Z_K(m)=e^{it_j\log m}\quad(B_j\leq m<B_{j+1}),           \tag{23}
\]

and choose any unit-circle values for `m<B_2`. Let `a_K=Re Z_K`, `b_K=Im Z_K`, and `z_K(n)=Z_K(c_K(n))`. By definition `z_K(sn)=z_K(n)` for every `s in S_K`, exactly, with no restriction on the size of `s`.

At `X_j=floor(B_{j+1})=floor(2t_j)`, compare `z_K(n)` to `e^{it_j log n}`. If `s_K(n)<=D` and `n>=D B_j`, then its core is in block `j`, apart from at most two positions at the upper boundary. The proportion of remaining positions up to `X_j+1` is at most

\[
 T_K(D)+D B_j/X_j+O(1/X_j)
       \leq T_K(D)+D/(2j)+o(1).
\]

Within block `j` the displacement is bounded as in (13), whose average tends to zero by (21). First let `j->infinity` with `D` fixed, then let `D->infinity`. The average endpoint displacement tends to zero. Consequently

\[
 J_K(X_j;a_K,b_K)\longrightarrow I(1/2).                 \tag{24}
\]

### 4.2 Exact coordinate assertions

Let `mu` be Haar probability measure on the unit circle. For every fixed `d>=1` and residue `r`, and every continuous circle function `psi`,

\[
 \frac dY\sum_{\substack{1\leq n\leq Y\\n\equiv r\ (d)}}
       \psi(z_K(n))\longrightarrow\int\psi\,d\mu.        \tag{25}
\]

For `u(n)=psi(z_K(n))-int psi dmu`, for every fixed `q,d>=1` and residue `r`,

\[
 \lim_{L\to\infty}\limsup_{Y\to\infty}
 \frac dY\sum_{\substack{1\leq n\leq Y\\n\equiv r\ (d)}}
 \left|\frac1L\sum_{\ell=1}^L u(n+q\ell)\right|^2=0.     \tag{26}
\]

This contains both ordinary SI and the fixed-progression version. All of `K,psi,q,d,r` are fixed before these limits. There is no assertion uniform in growing moduli, no assertion for every individual interval, and no quantitative rate stipulated. These are the same relevant coordinate quantifiers as in the known input.

Here is a proof at **all** scales, not just along `X_j`.

### 4.3 Truncation and the finite periodic decomposition

Fix `D` and `epsilon>0`. For positions in `[epsilon Y,Y+qL]`, first discard those with smooth part greater than `D`. Their proportion is at most `T_K(D)+o_Y(1)`. For averages restricted to `n=r mod d`, the elementary upper bound costs a factor `d`.

Put

\[
 Q_D=\prod_{p\leq K}p^{1+\lfloor\log D/\log p\rfloor}.
\]

For each `s in S_K`, `s<=D`, the condition `s_K(n)=s` is a union of residue classes modulo `Q_D`: it specifies each valuation exactly, including its first absent power. These are finitely many classes with a fixed modulus.

All retained cores lie in `[epsilon Y/D,2Y]` for large `Y`. Because `B_{j+1}/B_j->infinity`, this fixed-ratio interval intersects at most two blocks for all sufficiently large `Y`. For each `s<=D`, the block changes only at endpoints `s B_j`. There are only finitely many relevant endpoints, with a bound depending on `K,D,epsilon`, not on `Y`. Splitting the position interval at them and into residue classes modulo `lcm(Q_D,d)` reduces (25) to finitely many log-wave sums.

For (26), discard starting points within `qL+1` of those endpoints. For fixed `L` this costs `o_Y(1)`. On each remaining piece and each starting residue class, the allowed shifts for any given smooth part form fixed residue classes in `ell`, and each uses a fixed frequency `t_j` and the harmless factor `s^{-it_j}`. The number of such pieces and frequencies is bounded independently of `L,Y` once `K,D,epsilon,q,d` are fixed. Moreover, on every active piece,

\[
 \frac{\epsilon}{2D}Y\leq t_j\ll Y\log(2Y).              \tag{27}
\]

The lower bound uses `t_j=B_{j+1}/2>=m/2` for a core in its block, and the upper bound uses (22) and `B_j<=m<=2Y`.

### 4.4 The two oscillatory estimates needed for the proof

Both estimates below are uniform over subintervals of `[epsilon Y,2Y]` and a fixed progression. Frequencies obey (27).

For every fixed nonzero integer `h`, the second derivative test, with `|d^2(h t log x)/dx^2| asymp |h|t/Y^2`, gives

\[
 \sum_{n\in I,\ n\equiv a\ (M)}e^{ih t\log n}
       \ll_{h,M,\epsilon}\sqrt t+Y/\sqrt t=o(Y).          \tag{28}
\]

Indeed `t` lies between a positive constant times `Y` and `O(Y log Y)`. This is the elementary van der Corput second derivative bound `length*sqrt(lambda)+lambda^{-1/2}`, applied after parametrizing the progression. Subintervals can be used directly; they need not have a positive fraction of the full length. Formula (28), finite Fourier approximation, and the truncation errors prove (25).

For fixed `L` and `ell!=k` in `[1,L]`, put

\[
 \Phi(x)=h t[\log(x+q\ell)-\log(x+qk)].
\]

Its derivative has constant sign and monotone absolute value, and

\[
 |\Phi'(x)|=\frac{|h|tq|\ell-k|}{(x+q\ell)(x+qk)}.
\]

The first derivative integral bound therefore gives

\[
 \frac1Y\left|\int_I e^{i\Phi(x)}\,dx\right|
       \ll_{h,q}\frac{Y}{t|\ell-k|}
       \ll_{K,D,\epsilon,h,q}\frac1{|\ell-k|}.             \tag{29}
\]

Comparison of a fixed-progression sum with its integral has normalized error

\[
 O_{M,h,q,L,\epsilon}\left(\frac1Y+\frac{t}{Y^2}\right)
       =o_Y(1),                                         \tag{30}
\]

uniformly over the pieces: use the bound by `O_M(1+int |Phi'|)` for the unnormalized discrepancy. The constant density of the progression is retained in this comparison. Combining (29)--(30), and including the diagonal terms, proves for any subset of shift indices in fixed residue classes

\[
 \frac1Y\sum_{n\in I,\ n\equiv a\ (M)}
 \left|\frac1L\sum_{\substack{1\leq\ell\leq L\\
                          \ell\text{ in specified classes}}}
            e^{ih t\log(n+q\ell)}\right|^2
       \ll_{K,D,\epsilon,h,q,M}\frac{1+\log(2L)}L+o_Y(1). \tag{31}
\]

Here `Y->infinity` is taken with `L` fixed. To check the logarithm explicitly, the diagonal contributes at most `1/L`; the off-diagonal bound is a constant times
`L^{-2} sum_{ell!=k} 1/|ell-k| <= 2 L^{-1} sum_{h=1}^{L-1} 1/h`.

For a mean-zero trigonometric polynomial, apply (31) to its finitely many nonzero Fourier modes and to the finitely many periodic pieces; finite Cauchy--Schwarz handles their sum. There is no constant Fourier term. A continuous mean-zero `psi` is uniformly approximable by such polynomials.

Finally, truncation is harmless for this mean-square conclusion without a factor `L`: Jensen gives

\[
 \left|L^{-1}\sum_{\ell\leq L}v(n+q\ell)\right|^2
       \leq L^{-1}\sum_{\ell\leq L}|v(n+q\ell)|^2.
\]

For an error supported on the discarded positions, summing this inequality costs only `O_{psi,d}(epsilon+T_K(D))+o_Y(1)`. Take `Y->infinity`, then `L->infinity` in (31), then remove the polynomial approximation error, and finally let `epsilon->0` and `D->infinity`. This proves (26) with all its stated quantifiers.

### 4.5 Scalar labels, centering, and what has not been imposed

Let `theta(m)` be the argument of `Z_K(m)` in `[0,2pi)`, let `F` be the Dickman exponent CDF, and let `Q=F^{-1}`. Define

\[
 g_K(m)=Q(\theta(m)/(2\pi)).
\]

Then `g_K(c_K(n))` has marginal `F` in every fixed progression and satisfies the coordinate SI assertion for every continuous scalar test, and also for cutoff tests because `F` has no atoms. To justify the endpoint seam, approximate `psi(Q(theta/(2pi)))` in circle `L2` by continuous periodic functions. Formula (25), also for bounded functions whose only discontinuity is that seam, controls the mean-square approximation error; Jensen controls its short averages. Thus (26) transfers. The original two labels are functions of this one scalar label:

\[
 a_K=\cos(2\pi F(g_K)),\qquad b_K=\sin(2\pi F(g_K)).
\]

Their means are zero by (25), and (24) is unchanged. Alternatively, subtracting any constants from two labels changes their skew current only by endpoint terms. Centering is not a remedy.

There are even **fixed indicator labels** with these coordinate properties and positive limsup current. Apply (16)--(17) to this fixed pair along `X_j`. The integrands in (17) are bounded by 1, so reverse Fatou gives

\[
 \int_0^1\!\int_0^1\limsup_j
   J_K(X_j;1_{(1+a_K)/2>s},1_{(1+b_K)/2>t})\,ds\,dt
       \geq I(1/2)/4.
\]

Some fixed thresholds therefore have limsup at least `I(1/2)/4>=7/256`. Each such threshold function on the circle has only finitely many boundary points. The same `L2` approximation argument proves its centered SI/AP assertion at all scales. Thus the conditional counterexample is genuinely a cut obstruction too.

No full uniform growing-dilation inequality, diagonal nonconcentration, or cross-`K` compatibility is being claimed for this model. In fact any nonconstant scalar sequence exactly invariant under multiplication by 2 cannot satisfy the full pointwise inequality (U) for all multipliers: apply (U) to `2^r m` and multiplier `k`, then let `r->infinity`. Exact dyadic invariance would give `g(km)=g(m)` for all `k,m`, forcing constancy. This observation also explains why a core lift itself need not satisfy pointwise (U), even when it approximates an actual stable function in density.

The conclusion proved here is exactly that **coordinate SI/AP information plus exact invariance under the chosen finite smooth semigroup is insufficient for a uniform cut estimate**. Additional compatibility coming from actual LPF, or from an underlying function satisfying the full stability package, has not been discarded and then silently recovered.

## 5. Balanced smooth ratios, expansion, and nonbacktracking moments

The obstruction is intrinsic to the finite multiplication semigroup, not to the large-prime rectangle or its product-size cutoff.

For every fixed smooth ratio `u/v`,

\[
 |e^{it\log(u/v)}-1|
       \leq\sum_{p\leq K}|v_p(u)-v_p(v)|\delta_p(t).       \tag{32}
\]

Thus the characters used in section 2 become arbitrarily close to invariant under **any fixed finite family** of balanced smooth ratios, at the same time that their original-scale length-one current tends to the positive number (15). The valuation-weighted estimate (13) deals with the whole fibers, not only with a finite family of ratios. The labels on cores themselves are exactly constant on each smooth orbit.

It is true that products of fixed small-prime multipliers at a fixed moment order remain constant before `X->infinity`; the previous large-prime product-rigidity cutoff is not being applied here. Instead, high-frequency near-trivial characters of a finitely generated multiplication action survive. Compact recurrence supplies them at arbitrarily large frequencies comparable to the counting scale. Short additive averages of each coordinate still have mean zero by section 4; that does not make the adjacent coupling reversible.

Consequences for proposed tools:

* An unsigned expansion assertion, even if available for a related core graph, cannot imply the false signed cut conclusion (18).
* A trace or nonbacktracking argument proving `||B_X||=o_K(1)+o_X(1)` with normalization (7) is also impossible, by (19). Removing `o(X)` positional mass does not fix it.
* A balanced-ratio method must impose a restriction on the **labels**, or subtract/control these resonant modes using information stronger than coordinate SI/AP. Merely increasing a fixed moment order or adding finitely many smooth ratios does not do so: (32) holds for all of them simultaneously.

This is a counterexample to the proposed operator/cut conclusion, not an assertion that every variant of an arithmetic moment method is impossible. Label-specific LPF estimates could still avoid it.

## 6. The divisibility graph really gives an average of scales

Let `g(n)=a(c_K(n))`, `h(n)=b(c_K(n))`, and

\[
 j_q(n)=g(n)h(n+q)-h(n)g(n+q).
\]

For a prime set `P` contained in the primes at most `K`, exact smooth invariance gives, with `M_p=floor(X/p)`,

\[
 \frac1X\sum_{p\in P}\sum_{\substack{n\leq X\\p\mid n}}j_p(n)
       =\sum_{p\in P}\frac{M_p}{X}J_K(M_p;a,b).           \tag{33}
\]

When `M_p=0` the summand is zero. The definition here permits the endpoint `n+p` to exceed `X`, just as a prefix definition of `J_q` does. If both endpoints must lie in `[1,X+1]`, replace `M_p` by `max(0,floor((X+1)/p)-1)`; the total difference is `O(|P|/X)` for bounded labels. In a dyadic vertex interval there are instead the corresponding interval currents on `[X/p,2X/p]`.

The harmonic mass is

\[
 \mathcal L=\sum_{p\in P}1/p.
\]

Thus (33), normalized by `mathcal L`, is a harmonic **average of different scales**. It is not `J_K(X)`.

The counterexample makes this distinction quantitative, without appealing to a possible unknown behavior of LPF. Use the labels `a_{t_X},b_{t_X}` from (12), the **same** labels at all the smaller scales in (33). For each fixed `p<=K`, (13)--(14) give

\[
 J_K(\lfloor X/p\rfloor;a_{t_X},b_{t_X})\longrightarrow I(p/2).
\]

On the other hand, integration by parts gives, for `c>0`,

\[
 I(c)=c\int_c^\infty\frac{\sin v}{v^2}\,dv,
 \qquad |I(c)|\leq\frac2c.                              \tag{34}
\]

Indeed the integral equals `cos(c)/c^2-2 int_c^infinity cos(v)/v^3 dv`, whose absolute value is at most `2/c^2`. Consequently the absolute value of the limiting normalized expression (33) is at most

\[
 \frac1{\mathcal L}\sum_{p\in P}\frac{|I(p/2)|}{p}
       \leq\frac4{\mathcal L}\sum_{p\in P}\frac1{p^2}.    \tag{35}
\]

For example, take all primes at most `K`, first let `X->infinity` for each fixed `K`, then let `K->infinity`. Since `mathcal L->infinity` and `sum_p p^{-2}<infinity`, (35) tends to zero, while the original-scale current is always at least (15) in the limit. This is an explicit compatible example of **scale-averaged cancellation and noncancellation at the target scale**.

The fixed-label construction has the same property along `X_j`: for each fixed `p`, the lower block cutoff `B_j/(X_j/p)` tends to zero, and the proof of (24) gives the limit `I(p/2)` at `floor(X_j/p)`.

Choosing a narrow prime band to make the scales nearly equal does not retain a growing harmonic degree. For a fixed multiplicative band `[H,(1+eta)H]` its prime harmonic mass is `O_eta(1/log H)` (and is asymptotic to `log(1+eta)/log H` for fixed `eta>0`). The large-degree relative expansion gain cannot simply be kept after that restriction.

## 7. What Helfgott--Radziwill 2103.06853 actually says here

The local source `/corpus/src/2103.06853/trace.tex` was checked directly. To avoid confusing its parameters with the core cutoff, denote its exceptional-set parameter by `kappa`.

* `trace.tex:186--202` defines the **symmetric centered** operator on integer vertices `N<n<=2N`,
  \[
  H v(n)=\sum_{p\in P,\ \sigma=\pm1}
          (1_{p\mid n}-1/p)v(n+\sigma p),
  \]
  with both endpoints restricted to that interval. This is not `F^T(S-S^T)F` for the length-one path.
* `208--229`: its main theorem requires `mathcal L=sum_{p in P}1/p>=e`, a lower cutoff satisfying `log H_0 >= (log H)^{2/3}(log log H)^2`, and `log H <= sqrt(log N/mathcal L)`. For `1<=kappa<=log N/(mathcal L(log H)^2)`, it removes at most
  `O(N exp(-kappa mathcal L log kappa)+N/sqrt(H_0))` vertices and bounds the restricted norm by `O(sqrt(kappa mathcal L))`.
* `498--551`: short-edge locality is used to turn a large spectral value into many witnesses for the trace. The signed walk cancellation is produced by **centering the divisibility indicator**, eliminating singleton prime lengths. Skew-symmetrizing the core path is not that centering operation. Passing to core classes also identifies positions spread over the interval, rather than preserving short-edge locality.
* `325--360`: its correlation consequence explicitly contains `sum_{p in P} sum_{N/p<n<=2N/p}`; the accompanying discussion identifies logarithmic and almost-all-scale consequences. It does not turn this into an arbitrary fixed original-scale correlation.
* `7556--7563`: the alternative graph with edges `{n,n/p+1}` is explicitly mentioned as problematic because nonlinear divisibility relations quickly occur. There is no claimed black-box theorem for all multiplication/division quotient graphs.

Even a suitable **forward-edge** decoupling derived from a divisibility-graph result would still have (33) on its divisible-edge side. Also, the displayed symmetric operator itself has identically zero antisymmetric bilinear form; extracting a directed version is an additional step, not an identification of the operators. Regardless of that issue, (35) already rules out the suggested passage from its normalized scale average to the desired uniform fixed-scale conclusion.

For the small-core setting the HR size restrictions need not be the main problem: finite prime sets are eventually small relative to `N`. The decisive obstruction to the proposed generic conclusion is instead the actual label construction (2), or (24)--(26) when coordinate assumptions are included.

## 8. Precisely delimited outcome and audit record

The following route is now rigorously excluded:

> Approximate LPF by its fixed-small-prime-core lift; forget the special labels; prove fixed-scale skew cancellation uniformly for bounded core labels, perhaps assuming only their coordinate short-interval/AP mean-zero properties; then send the prime cutoff to infinity.

The forgetting step requests a false theorem. The counterexamples are on the actual quotient of the integer path, handle all finite prime cutoffs, have positive normalized cut mass, survive degree-correct negligible trimming, and can satisfy the stated coordinate assumptions at all scales with fixed labels.

A remaining label-specific route would have to exploit restrictions not present in that class. In particular, actual labels for different `K` are compatible restrictions of the same function `f`, and the original `f` satisfies the full uniform growing-dilation inequality. Neither feature is asserted for the counterexamples. Nothing here proves that those stronger restrictions fail to force reflection, and no result on the ordinary LPF ascent density is claimed.

One additional necessary restriction can be stated exactly. For actual lifted labels `A_K(n)=phi(f(c_K(n)))`, with fixed continuous `phi`, every fixed integer `q>=1`, including those with prime factors above `K`, satisfies

\[
 \frac1X\sum_{n\leq X}|A_K(qn)-A_K(n)|\longrightarrow0.   \tag{36}
\]

This follows by inserting `phi(f(qn))` and `phi(f(n))`, using section 1.1 at scales `qX` and `X` (restriction to multiples costs the fixed factor `q`), and using (U) for the middle difference. Assertion (36) for all `q` is **not** claimed for the fixed-label model in section 4. Thus this note does not rule out a theorem additionally using all-scale, all-fixed-multiplier compatibility, still less the quantitative growing-multiplier package. Conversely, at a chosen witness scale any prescribed finite collection of extra multiplier constraints can be respected by the section 2 construction: simply include their prime factors in the finite recurrence list. This last observation is not a substitute for (36) at every scale for one fixed labeling.

Verification consists of the displayed proofs, not numerical evidence:

* The finite identities (7)--(10), (13), (16)--(17), and (33) retain the endpoint and degree normalizations.
* The recurrence proof is compactness for a finite torus orbit, with all `K`-dependent thresholds left explicit.
* The positive lower bound is the rational certificate (15); no numerical integral is used.
* The fixed-label construction and the SI proof use separate limits in the required order. Tail errors use (4)--(5), interval-boundary errors vanish with `Y` for fixed `L`, and the off-diagonal mean-square estimate is (29)--(31).
* No conclusion about the original scale is drawn from a prime average; (34)--(35) explicitly demonstrate why that inference fails.
* Exact symbolic checks in `python3` passed for the rational certificate (15), the centering identity (16), the derivative in (29), and the integration-by-parts identity (34). These check algebra; the asymptotic proofs are the arguments above. Display delimiters were checked as well.
* `Submission/Spec.lean` was not edited. Its SHA-256 was rechecked after writing this note and remains `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`. No admitted statement from it, and no purported resolution of its targets, enters any proof above.

## Independent audit and a further quantifier boundary

The main assistant independently checked the compact recurrence argument, the valuation-weighted finite bound (13), the rational lower certificate, the graph-mass normalization, the fixed-block construction, and both oscillatory estimates with their limit order. The exact HR operator and theorem hypotheses were read directly in `trace.tex:186--229,325--360`.

The coordinate SI assertion in this note has **K fixed before the limits**; its proof supplies constants depending on K and the smooth-part truncation. It does not supply a common SI modulus uniform over the different counterexamples as K tends to infinity. This matters for a possible strengthened route: actual LPF lifts for different K are all L2-close in density to the same original sequence, for each fixed K. Hence for each fixed L their limiting short-interval mean-square energy equals that of the original sequence, by Jensen and Cauchy--Schwarz, and those limiting energies have a common modulus independent of K. The counterexamples above are not claimed to satisfy this additional cross-K requirement. Thus the note does not refute a theorem that genuinely uses such uniform compatibility, or the all-fixed-multiplier condition (36), rather than just the individually stated coordinate assumptions. The growing-multiplier functional in `GrowingMultiplierResearch.md` is a separate, still-unproved candidate addressing stronger stability; its bounded cut estimate is not refuted by this note.
