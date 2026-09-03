# Many-factor critical-band audit

**Status:** Analytic upper bounds and exact decompositions only. Neither theorem in `Spec.lean` is proved or used. The signed remainder remains uncontrolled. The main assistant independently checked the estimates below against `CriticalBandSieveResearch.md`, including its per-box sieve uniformity, and the actual kernel in `DirectOddCountResearch.md` §13.

## 1. Normalization and row bound

Write
\[
 L=\log X,\quad P=X^{.6},\quad D=V=X^{.45},\quad Q=DV=X^{.9},\quad B=X^{.1},\quad z=X^{.14}.
\]
Use exactly
\[
 R=\sum_{d,v}\mu(d)u(d/D)\beta(v)K(d,v),\qquad
 \beta(v)=b_z(v)w(v/V),\quad b_z(v)=\sum_{e\mid v,e>z}\Lambda(e),
\]
\[
 K(d,v)=\sum_{p\sim P}\log p\sum_{b\ge1}
 W(p/P,dv/Q,b/B)(1_{p\mid bdv-1}-1_{p\mid bdv+1}).
\]
Here the prime sum is over primes, the fixed cutoffs satisfy `|u|<=1`, `0<=w<=1`, and `W` is odd and uniformly Schwartz in its final coordinate. Let `K+` replace the difference by a sum and `W` by `|W|`; let `E(S)` denote the resulting positive first-moment envelope on a sector `S`. Uniformly,
\[
 |W(r,t,x)|\ll_J\psi_J(x):=x(1+x)^{-J-1},\quad K^+(d,v)\ll BL.
\]
The entire tail `b>BX^epsilon`, for fixed `epsilon=1/200`, costs `O_A(X^{-A})` after choosing sufficiently large fixed Schwartz order. This uses `sum_{p|bdv±1}log p<=log|bdv±1|` and summation of the whole weighted tail, not a bound on its individual summands. All following statements absorb this tail.

Put `a(t)=t/phi(t)`. Elementary nonnegative divisor expansions give
\[
 \sum_{t\le T}a(t)^j\ll_j T\quad(j=1,2),\qquad
 \sum_b\psi_J(b/B)a(b)\ll_J B.
\]
Indeed the divisor coefficient at a prime is `(1-1/p)^{-j}-1=O_j(1/p)`, so its harmonic sum converges. Also `a(xy)<=a(x)a(y)`.

Fix `b,v`, put `m=bv`, and write `md-ap=sigma`. The quotient has `a~mD/P`, a range with `O(mD/P)` terms since this quantity is at least a fixed multiple of `X^.3`. Necessarily `(a,m)=1`, and `p=-sigma/a mod m`. On the truncation `m<<X^(.55+epsilon)<P` by a fixed-power margin. Brun--Titchmarsh gives weighted prime mass `O(P/phi(m))` per quotient. The integer `d` is then determined. Summing the quotients and the `b`-weights proves
\[
 G(v):=\sum_{d\sim D}|u(d/D)|K^+(d,v)\ll DBa(v). \tag{1}
\]
The same argument with `d=rn` and modulus `bvr`, for prime `r<=X^.001`, gives
\[
 \sum_n|u(rn/D)|K^+(rn,v)\ll (DB/r)a(rv). \tag{2}
\]
The analogous bound with `v=rm` holds with the variables exchanged and their corresponding cutoffs.

The compatible original second moment therefore satisfies
\[
 M=\sum_v\beta(v)|\sum_d\mu(d)u(d/D)K(d,v)|^2
 \ll VD^2B^2L=X^{31/20}L. \tag{3}
\]
Use `b_z(v)<=log v` and the mean-square bound for `a(v)`; no independence of these factors is assumed. The required threshold remains `M=o(X^{31/20}/L)`. Thus (3) is not enough.

## 2. A complete but not cancellative extraction partition

Set
\[
 y_0=L^{12},\quad Y=X^{.001},\quad I=\{r\text{ prime}:y_0<r\le Y\},
\]
and let `omega_I` count distinct `I`-prime factors.

The **simultaneous zero set** `omega_I(d)=omega_I(v)=0` has envelope
\[
 E_0\ll X(\log L)^2/L=o(X). \tag{4}
\]
Here is the full justification. Factor out the full `y_0`-smooth parts `d=am,v=cn`, including multiplicities. On this sector both residuals are `Y`-rough. For a smooth part exceeding `X^.01`, Rankin with exponent `1/24` gives
\[
 \sum_{P^+(a)\le L^{12},\ a>X^{.01}}1/a
 \le X^{-1/2400}\prod_{p\le L^{12}}(1-p^{-23/24})^{-1}
 \le X^{-1/2400}\exp(O(\sqrt L)).
\]
For the last bound even summing `t^{-23/24}` over all integers `t<=L^{12}` suffices. Counting multiples, applying `K+<<BL`, and `beta<<L` makes these tails power-saving. For retained `a,c<=X^.01`, apply the uniform two-parameter sieve of `CriticalBandSieveResearch.md` (17) with roughness thresholds `Y,Y` and fixed sieve level `xi=X^.005`. Its bound is
\[
 E_{a,c}(Y,Y)\ll (X/L)\mu^2(a)f(a)f(c)/(ac),\quad
 f(t)=\prod_{p\mid t,p>2}(p-1)/(p-2).
\]
Both smooth harmonic Euler products are `O(log y_0)=O(log L)`, giving (4). This proof does NOT delete the union where either one of the two variables has no `I` factor.

Pairs with `r^2|v` for some `r in I` have envelope
\[
 \ll XL^2\sum_{r>y_0}r^{-2}\ll XL^2/y_0=o(X), \tag{5}
\]
by counting multiples in the fixed dyadic block and the pointwise envelope. `mu(d)` already removes repeated factors of `d`.

Thus, up to `o(X)`, the two **disjoint** branches are:

* `d` has an `I`-factor;
* `d` has none, but `v` has an `I`-factor and is squarefree at `I`.

A calculation extracting from both variables covers only the subset where both have a factor; it is not a replacement for this partition.

## 3. Exact single-variable Ramaré pieces and easy covariances

On `omega_I(d)=k>=1`, and a dyadic prime interval `I_T`, the first branch is the sum of the exact pieces
\[
 S^d_{k,T}=-\frac1k\sum_{\omega_I(n)=k-1}\mu(n)\sum_v\beta(v)
 \sum_{r\in I_T,\ r\nmid n}u(rn/D)K(rn,v). \tag{6}
\]
Retain any previously imposed restriction on `v`, notably the squarefree-at-`I` indicator, in its external weight. The minus sign and denominator follow from `mu(rn)=-mu(n)` and exact counting of the `k` prime divisors. The `n`-range is a fixed multiple of `D/T`. Weighted Cauchy gives
\[
 |S^d_{k,T}|^2\ll \frac{QL}{Tk^2}M^d_{k,T},\quad
 M^d_{k,T}=\sum_{\omega_I(n)=k-1}\mu^2(n)\sum_v\beta(v)
 \left|\sum_{r\in I_T,r\nmid n}u(rn/D)K(rn,v)\right|^2. \tag{7}
\]
For the second branch write `v=rm`. The exact identity `b_z(rm)=b_z(m)` holds because `r<z` and `r` has exponent one. The corresponding formula is (6) with no new minus sign, with external `mu(d)u(d/D)1_{omega_I(d)=0}`, with external `b_z(m)` and the squarefree-at-`I` restriction, and inner `w(rm/V)K(d,rm)`. Its Cauchy factor is again `O(QL/(Tk^2))`. The cutoffs must not be replaced by ones at the unscaled residual variable.

For either norm in (7), the repeated-extracted-prime diagonal is
\[
 M_{r=s}\ll XB L^2/\log T. \tag{8}
\]
To see this, bound one `K+` by `BL`; sum the remaining first moment on `r|d` using (2), `beta<=L`, and `sum_v a(v)<<V`; then sum `1/r` on `I_T`, which is `O(1/log T)`. The symmetric proof applies to extraction from `v`, using the bound `b_z(m)<=L`.

For `r!=s` but the same prime modulus `p`, both congruences imply
\[
 \sigma_2b_1r=\sigma_1b_2s\pmod p.
\]
On the truncation both positive products are much smaller than `p`, so `sigma_1=sigma_2` and `b_1r=b_2s`. Consequently `b_1=st,b_2=rt`. Put `A=trsn`. On the nonempty supports `A<<DBX^epsilon<P` by a fixed-power margin, and `AV/P` is a positive power of `X`. The same quotient/Brun--Titchmarsh argument, now with the two prime logs and `beta<=L`, gives
\[
 \sum_{v\sim V}\beta(v)\sum_{p\mid Av-\sigma}(\log p)^2
 \ll VL^2a(A).
\]
Summing `a(n)` on `n<<D/T`, summing `a(t)psi_J(ts/B)psi_J(tr/B)` (which is `O(B/T)` since `r,s~T<=Y<B`), and using `#I_T<<T/log T`, proves
\[
 |M_{p_1=p_2,\ r\ne s}|\ll XL^2/(\log T)^2. \tag{9}
\]
The symmetric extraction has exactly the same bound. No equality of the two smooth factors is used.

Both (8) and (9) are genuinely negligible after (7) and summation of the pieces. For example, the square-root contribution of (8) is at most
\[
 \frac{XL^{3/2}}{k\sqrt{T\log T}}.
\]
Sum geometrically over the dyadic `T>=L^{12}`, and harmonically over `k<=O(L/log L)`, to get `O(XL^{-9/2}sqrt(log L))`. Bound (9) has an additional power saving relative to this. This does not control the remaining covariance.

In that remainder `r!=s`, `p_1!=p_2`, and the actual four-sign factor is
\[
 \sum_{\sigma_1,\sigma_2=\pm1}\sigma_1\sigma_2
 1_{p_1\mid b_1rnv-\sigma_1}1_{p_2\mid b_2snv-\sigma_2}. \tag{10}
\]
The exact coefficients, restrictions and two rescaled kernels from (7) remain. Its complete mean is zero, but the original intervals do not cover the product period. No bound sufficient to sum (7) is proved for (10).

## 4. A limited growing-factor-count deletion

For each fixed `0<c<.37336`, put `k=c log L` and `y=X^{gamma/k}`, with fixed `gamma=.01`. On `Omega(d)+Omega(v)<=k`, extract the full `y`-smooth parts `d=am,v=bn`. Both are at most `X^gamma`; both residuals exceed one, so `Omega(a)+Omega(b)<=k-2`.

Keep the sieve level `xi=X^.005` fixed. The box-length margin in `CriticalBandSieveResearch.md` is `tau=.05-epsilon-gamma=.035`. The relative box remainder is
`O(L^104(X^{-.025}+X^{-.05}))=o(L^{-3})`, uniformly in `y`, and the survival product is at least a fixed multiple of `L^{-3}`. Therefore the error is absorbed per box before cofactor summation; constants do not secretly depend on growing `k`. Eventually `y<xi`.

The sieve and a Rankin parameter `0<t<1` now give
\[
 E(\Omega(d)+\Omega(v)\le k)
 \ll\frac{XL}{(\log y)^2}
 t^{-(k-2)}\prod_{p\le y}(1+tf(p)/p)(1+tf(p)/(p-t))
 \ll_t XL(\log y)^{2t-2}t^{-(k-2)}.
\]
The second local factor includes all multiplicities in `b`. Take `t=c/2` to obtain
\[
 E(\Omega(d)+\Omega(v)\le c\log L)
 \ll_c X L^{-\eta(c)}(\log L)^{2-c},\quad
 \eta(c)=1-c(1+\log(2/c))>0. \tag{11}
\]
This does not bound the typical or high-factor-count remainder. It is a new uniform argument, not substitution of a growing parameter into a bound with uncontrolled factor-count constants.

## 5. Regrouping is not logarithmic smoothing

The exact coefficient on `q=dv` is
\[
 \gamma(q)=\sum_{d\mid q}\mu(d)b_z(q/d)u(d/D)w(q/(dV)).
\]
If `S` is a product of exponent-one primes at most `z` dividing `q`, and `q=St`, the small-prime finite difference reads
\[
 \gamma(q)=\sum_{a\mid t}\mu(a)b_z(t/a)
 \sum_{e\mid S}\mu(e)u(ae/D)w(q/(aeV)).
\]
The differentiable function is `F_q(s)=u(exp(s)/D)w(q/(V exp(s)))` in `s=log d`. The finite-difference bound is `||F_q^(j)||infty prod log r`, NOT `prod(log r/log D)`. Reparametrizing by `log d/log D` multiplies the derivatives by `(log D)^j`.

Independently checked source: Granville--Koukoulopoulos--Maynard, `/corpus/src/1606.06781/1606.06781.tex`, lines 137--164 (derivatives), 315--330 (positive limiting constant in the dyadic Möbius-divisor second moment for averaging length at least the square of the cutoff), and 351--370 (fixed smooth logarithmic weight). Those results do not provide a vanishing moment for the present dyadic coefficient. Opening `b_z` may also leave averaging length `Q/z=X^.76<D^2=X^.9`, so the long-average moment theorem cannot be applied indiscriminately.

**Remaining gap:** signed cancellation in (10), or another compatible estimate for the unrestricted many-factor functional, is still absent. The full density theorem additionally requires all remaining exponent and frequency regions. No `o(X)` theorem for even the complete pilot follows from this audit.
