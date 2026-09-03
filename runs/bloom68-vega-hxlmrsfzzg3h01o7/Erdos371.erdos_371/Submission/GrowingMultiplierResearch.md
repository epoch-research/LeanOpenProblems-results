# Growing multiplier averaging: a genuine fixed-scale reduction with an unproved cut bound

**Status:** Neither target theorem is proved. This is a new candidate estimate and an audit of several possible substitutes, not a claim that the estimate holds. No admitted target is used. The main assistant independently checked all algebra below and the precise external statements of the derivative test, the determinant corollary, and the fixed-linear-form prime theorem.

## 1. The exact bounded-label functional and LPF reduction

For positive integers `X,H`, let `N=H(X+1)` and define
\[
 A_HF(n)=H^{-1}\sum_{k\le H}F(kn),\qquad 1\le n\le X+1,
\]
\[
 C(X,H;F,G)=\frac1X\sum_{n\le X}
 [A_HF(n)A_HG(n+1)-A_HG(n)A_HF(n+1)]. \tag{1}
\]
The labels are defined through the full endpoint `N`. Unlike the divisible-edge prime average, this is an average whose base variable stays at the original scale `X`.

For actual `f(n)=log P(n)/log n`, bounded Lipschitz tests `phi,psi`, and `F=phi o f,G=psi o f`, the already kernel-checked stability inequality gives, for `epsilon X>=2`,
\[
 |J_X-C(X,H;F,G)|
 \le4M_\phi M_\psi(\epsilon+O(1/X))
 +2(M_\psi L_\phi+M_\phi L_\psi)
       \frac{\log H}{\log(H\epsilon X)}. \tag{2}
\]
Here `J_X` is their ordinary adjacent antisymmetric product mean, `M` are supremum norms and `L` Lipschitz constants. On `n>=epsilon X`, bound each averaging error by the maximum of `log k/log(kn)`, attained at `k=H`; both endpoints obey the same bound. The initial segment costs the displayed bounded error.

For `H=floor(X^delta)`, the logarithmic ratio tends to `delta/(1+delta)`. Consequently the still-unproved estimate
\[
 \lim_{\delta\downarrow0}\limsup_{X\to\infty}
 \sup_{|F|,|G|\le1}|C(X,\lfloor X^\delta\rfloor;F,G)|=0 \tag{3}
\]
would force the actual product-test current to vanish. The known near-diagonal nonconcentration would then supply the ordering reduction. A bound `C=o_delta(1)` for each fixed small positive `delta` is stronger than necessary. **Neither form of (3) is proved here.**

## 2. Exact matrix normalization

Let `M(n,a)=1` if `a=kn` for some `1<=k<=H`, and zero otherwise, for rows `1<=n<=X+1`, columns `1<=a<=N`. Let `J(n,n+1)=1`, `J(n+1,n)=-1`, for `n<=X`. Put
\[
 D=M^TJM,\qquad B=D/H^2=A_H^TJA_H.
\]
Then, with no missing endpoint,
\[
 C=F^TBG/X. \tag{4}
\]
The desired result is a **bounded cut norm** assertion. It must not be replaced by an incorrectly normalized Euclidean norm estimate.

## 3. A bulk obstruction to counting-measure l2 decay

For all integers `X>2H^2`,
\[
 \boxed{H\|B\|\ge\sqrt{2(X-2H^2)/(X+1)}.} \tag{5}
\]

Proof: an incidence `a=kn,b=l(n+1)` can have an opposite incidence only if
\[
 kn=l'(n'+1),\qquad l(n+1)=k'n'.
\]
Eliminating `n'` gives
\[
 (kk'-ll')n=l'(l+k')\le2H^2.
\]
The right side is positive, so the integer coefficient is positive and `n<=2H^2`. Thus every one of the `(X-2H^2)H^2` later incidences is unopposed and is not a loop. If several share the same ordered pair, squaring their positive integer multiplicity only increases its contribution. Including transposed entries yields
\[
 \|D\|_F^2\ge2(X-2H^2)H^2.
\]
Since `rank D<=X+1`, (5) follows.

For the normalized ambient norm `||F||_{2,av}^2=N^{-1}sum|F|^2`, the best bilinear coefficient in (4) is `(N/X)||B||=((X+1)/X)H||B||`. It does not tend to zero if `H=o(sqrt X)`. On the other hand, Schur's bound gives `||B||<=2d_max/H`, where `d_max` is the largest column multiplicity. The divisor bound even makes this last, **unnormalized** norm tend to zero at polynomial `H`. Forgetting the factor `H` would create a false saving.

This l2 obstruction does not prove a nonvanishing bounded cut norm. Singular vectors need not be usable as bounded labels with the required mass.

## 4. Incidence-normalized l2 still has thin obstructions

Let `d(a)=sum_n M(n,a)`, `W=diag d`, and `mu(a)=d(a)/(H(X+1))` on nonempty columns. Jensen shows `T=M W^{-1/2}/sqrt H` has norm at most one. Define
\[
 K=T^TJT=H^{-1}W^{-1/2}DW^{-1/2}.
\]
Then
\[
 |C|\le((X+1)/X)\|K\|\|F\|_{L^2(\mu)}\|G\|_{L^2(\mu)}. \tag{6}
\]
For any integer function `H=o(X)`, an absolute positive lower bound on `limsup_X ||K||` follows from a thin explicit witness. Here is the argument, with its external input identified.

There are arbitrarily large finite sets of distinct positive slopes satisfying `gcd(a,b)=|a-b|` for distinct members. Starting from `{1}`, replace a set `S` by `{L} union {L+s:s in S}`, taking `L` divisible by every member and every nonzero difference of `S`. A direct gcd calculation preserves the property.

Maynard's fixed admissible linear-form theorem, `/corpus/src/1405.2593/Subsets.tex:82--88`, with `m=2,y=x`, gives infinitely many parameters where two forms `at+1,bt+1` in a sufficiently large such fixed family are prime. The family is admissible because `t=0` makes every form one modulo every prime; all fixed positive slopes eventually meet the theorem's logarithmic coefficient bound. Write the prime values as `p=at+1<q=bt+1`. With `d=b-a`, put `u=b/d,v=a/d`, so `u-v=1` and `up-vq=1`.

At `X=vq=up-1`, eventually `H<min(p,q)` and `pq>2X+1`. Take bounded labels `F=1_{q|m}`, `G=1_{p|m}`. Then `A_HF(n)=1_{q|n}` and `A_HG(n)=1_{p|n}`. Their sole forward edge is `n=X`, and their first reverse edge would be `pq-X-1>X`. Therefore
\[
 C=1/X,\qquad \|F\|_{L^2(\mu)}^2=v/(X+1),\quad
 \|G\|_{L^2(\mu)}^2=u/(X+1).
\]
Equation (6) gives `||K||>=1/sqrt(uv)`. There are only finitely many slope pairs, so this supplies a fixed positive constant.

**Limitation:** the current is only `1/X`, and both incidence masses are `O(1/X)`. These witnesses are legitimately trimmable. Erasing labels on incidence mass `mu(E)` changes a bounded current by at most `4(X+1)mu(E)/X`. This is not a counterexample to (3), and is not an LPF label construction.

## 5. Moment rigidity has surviving affine relations

For an `r`-step closed walk, write
\[
 m_i=k_i n_i,\qquad m_{i+1}=l_i(n_i+\sigma_i),\quad
 k_i,l_i\le H,\quad \sigma_i\in\{-1,1\}.
\]
If all source positions are at least `epsilon X`, multiplying around the cycle gives
\[
 \prod k_i/\prod l_i=\prod(1+\sigma_i/n_i),
\]
\[
 |\prod k_i-\prod l_i|
 \le\frac{rH^r}{\epsilon X}\exp(r/(\epsilon X)). \tag{7}
\]
For fixed `r,epsilon` and `H=X^delta`, `delta r<1` forces equality of the two integer products. A trace of order `2m` is in this elementary rigidity range only if `2m delta<1`.

Equality does not eliminate nonbacktracking walks. For every `n>1,H>=2`, the actual incidence graph has
\[
 n\longrightarrow n+1\longleftarrow2n
 \longrightarrow2(n+1)\longleftarrow n.
\]
All four positive incidences have original base `n`; viewed along the cycle the signs are `+,-,+,-` and their product is positive. Both multiplier products are four, and the composed affine map is identically the identity. These fibre bicliques must be counted, not declared to cancel.

## 6. The finite-core resonant logwave is eliminated at polynomial H

For `M_H(t)=H^{-1}sum_{k<=H}k^{it}`, and `F(m)=cos(t log m),G(m)=sin(t log m)`, exact algebra gives
\[
 C=|M_H(t)|^2\frac1X\sum_{n\le X}\sin(t\log(1+1/n)). \tag{8}
\]
Unlike the fixed-core recurrence, for every fixed `0<delta<1/2` and fixed `0<c_1<c_2`,
\[
 \sup_{c_1X\le|t|\le c_2X}|M_{\lfloor X^\delta\rfloor}(t)|\longrightarrow0. \tag{9}
\]

A precise classical derivative bound is recorded in Heath-Brown, `/corpus/src/1601.04493/1601.04493.tex:16--26`. For an order `r>=2`, derivative size `lambda`, and bounded derivative-size ratio, it bounds a length-`L` exponential sum divided by `L` by
\[
 O_r(\lambda^{1/(2^r-2)}+L^{-2^{2-r}}\lambda^{-1/(2^r-2)}).
\]
On dyadic subintervals of `[alpha H,H]`, `lambda~_r |t|/H^r`. Choose `r=floor(1/delta)+2`, set `d=delta r-1`, `a=1/(2^r-2)`, `b=2^{2-r}`. Then `delta<d<=2delta`, and both `da` and `delta b-da` are positive, since `b/a=4-2^{3-r}>2`. The resulting saving is a fixed positive power of `X` for each fixed `alpha,delta,c_1,c_2`. The omitted `k<alpha H` cost at most `alpha`. Let `X` grow, then `alpha` decrease. Negative derivative signs are handled by complex conjugation. This proves (9).

Thus a frequency comparable to `X` cannot make all `k^{it}` near one for `k<=X^delta`. This removes the **particular** resonant-logwave mechanism in `SmallPrimeCoreGraphResearch.md`. It does not bound arbitrary bounded labels, much larger frequencies, or all possible Mellin superpositions.

## 7. The determinant benchmark does not close the cut estimate

Writing `a=kn,b=l(n+1)` gives `la-kb=-kl`; after exchanging `k,l` in the reversed term its determinant is `+kl`. This determinant depends on both short variables. If `(k,l)>1`, the extra divisibility conditions `k|a,l|b` must also be kept. Fixing `Delta=kl` inserts a coupled short-variable restriction; it does not leave separate smooth weights.

Bettin--Chandee's determinant corollary, `/corpus/src/1502.00769/1502.00769.tex:79--90`, requires a fixed nonzero determinant and separate smooth short weights. It is therefore not presently applicable to (1). Even the more favorable auxiliary fixed-determinant problem with short scales `H,H` and long scales `HX,HX` has their error
\[
 O_\epsilon((HX)^{39/20+\epsilon}).
\]
The factors are `(HX)` for the two bounded-label l2 norms, `(HX)^{7/10}` and `(HX)^{1/4}`. Dividing by the desired `XH^2` gives `X^{19/20}H^{-1/20}` up to the small-power factor, not a saving for small `delta`. This is a failed numerical benchmark, not a claim that the coupled determinant already meets their hypotheses.

**Remaining obligation:** (3), equivalently a sufficiently small bounded bilinear cut norm for `D`, is still unproved. The l2 substitutes are false, the finite-core counterexample does not extend in its original form, and the displayed moment and determinant arguments do not decide the bounded-label question. No conclusion about the target density follows from this note.
