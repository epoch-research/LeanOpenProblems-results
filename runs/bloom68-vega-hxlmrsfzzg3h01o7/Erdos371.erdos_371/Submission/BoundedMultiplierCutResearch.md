# Bounded multiplier cut: an annihilated class and the unresolved rough-core cut

**Status.** The full bounded cut estimate is **not proved**, and no positive-mass counterexample at polynomial `H` is constructed. There is a new direct cut estimate below: a bounded periodic function times a Mellin wave has negligible pairing with **every bounded second label**, uniformly in a small growing modulus and a superpolynomial frequency window. This gives an incidence-weighted approximation inverse, not an inverse theorem for all bounded labels. The exact remaining character and rough-core problems are stated in section 5.

The growing-multiplier note and the final cross-`K` warning in the small-prime-core note were read. No uniform cross-`K` conclusion is inferred from their fixed-`K` models. No admitted target is used; `Spec.lean` is unchanged.

## 1. Normalization and the new bounded-cut theorem

Put `Y=X+1`, `N=HY`, and retain exactly
\[
 A_HF(n)=\frac1H\sum_{k\le H}F(kn),\qquad
 C(F,G)=\frac1X\sum_{n\le X}
 [A_HF(n)A_HG(n+1)-A_HG(n)A_HF(n+1)].
\]
We also use its complex bilinear extension. Define
\[
 \mathcal S_{Y,H}=\{kn:k\le H,\ n\le Y\},\quad
 \sigma=\frac{|\mathcal S_{Y,H}|}{HY},\quad
 d(a)=\#\{(k,n):k\le H,n\le Y,kn=a\},\quad
 \mu(a)=\frac{d(a)}{HY}.                                      \tag{1}
\]
In particular `mu` is a probability measure, and `sigma>=1/H`.

Write
\[
 \gamma=1-\frac{1+\log\log2}{\log2}>0,\qquad
 T_H=\exp\!\left(\frac{\log H\log\log H}{8\log2}\right),\qquad
 E_H=\exp(-\sqrt{\log H}/64).
\]
All assertions involving these expressions are for sufficiently large `H`.

**Theorem (one-label periodic–Mellin cut bound).** Suppose `H<=X`, `q<=H^(1/6)`, and `p` is any complex `q`-periodic function with `|p|<=1`. For `|t|<=T_H`, set `F(m)=p(m)m^(it)` on the full interval `[1,N]`. Uniformly over `|G|<=1`,
\[
 |C(F,G)|\ll
 (q\sigma)^{1/3}
 +\frac{q\log H}{\sqrt H}
 +\frac{H^{1/3}\log(2X)}X+E_H.                              \tag{2}
\]
The implicit constant is absolute. For `H=floor(X^delta)`, any fixed `0<delta<1`, and `q<=(log H)^beta`, `0<=beta<gamma`, this implies
\[
 \sup_{p,t,G}|C(p(m)m^{it},G)|
 \ll (\log H)^{-(\gamma-\beta)/3}(\log\log H)^{-1/2}+o(1),   \tag{3}
\]
where the omitted terms are the explicit faster-decaying terms in (2). The frequency window `T_H` eventually exceeds `X^B` for **every fixed** `B`.

For a plain Mellin wave the sharper, support-independent bound is
\[
 \sup_{|t|\le T_H,\ |G|\le1}|C(m^{it},G)|
 \ll \frac{\sqrt H\log(2X)}X+E_H.                          \tag{4}
\]
Thus the conclusion concerns an arbitrary second label, not just a matched sine/cosine pair. It also concerns bounded cut mass, not a proposed global Euclidean operator norm.

## 2. The cancellation input that makes support sparsity useful

Here is the additional input; support sparsity **alone** would not prove (2).

**Signed-divisor lemma.** If `h` is `q`-periodic and odd (`h(-n)=-h(n)`), then, for real `t`,
\[
 S_{h,t}(a)=\sum_{\substack{kn=a\\k\le H,\ n\le Y}}h(n)n^{it}
 \quad\Longrightarrow\quad
 \sum_a|S_{h,t}(a)|^2\ll
 q(1+|t|)HY\|h\|_\infty^2.                                \tag{5}
\]
Consequently, by Cauchy–Schwarz on the actual support,
\[
 \frac1{HY}\sum_a|S_{h,t}(a)|
 \ll\|h\|_\infty\sqrt{q(1+|t|)\sigma}.                    \tag{6}
\]

**Proof of (5).** Parametrize an equality `kn=lm` uniquely by
`k=dr,l=ds,n=su,m=ru,(r,s)=1`. Writing `j=max(r,s)`, the square sum is exactly
\[
 H\sum_{u\le Y}|h(u)|^2+
 2\Re\sum_{2\le j\le\min(H,Y)}\!\lfloor H/j\rfloor
 \sum_{u\le Y/j}h(ju)j^{it}
 \sum_{\substack{r<j\\(r,j)=1}}\overline{h(ru)}r^{-it}.    \tag{7}
\]
For every integer `b`, `h(bv)` has period `q` and mean zero over that period: pair `v` with `-v`. Its partial sums are bounded by `q||h||_infty`. Möbius inversion for `(r,j)=1`, followed by partial summation, therefore bounds the inner sum in (7) by
\[
 q\|h\|_\infty\tau(j)(1+|t|\log j).
\]
Now use `floor(H/j) floor(Y/j)<=HY/j^2` and convergence of both
`sum tau(j)/j^2` and `sum tau(j) log(j)/j^2`. This proves (5). The saving in (6) is obtained only **after** this signed cancellation; there is no assertion that (5) holds for arbitrary tests `h`.

For completeness, the precise rectangular support input is
\[
 \sigma\ll (\log H)^{-\gamma}(\log\log H)^{-3/2}
 \qquad(Y\ge H).                                         \tag{8}
\]
It follows from Ford's upper bound for the count of integers `a<=z` having a divisor in `(y,2y]`, valid for `3<=y<=sqrt(z)`:
`O(z (log y)^(-gamma) (log log y)^(-3/2))`.
Partition the multiplier `k` into `(H/2^(j+1),H/2^j]` down to size `sqrt H`. A product from this bin is at most `HY/2^j` and has a divisor in that bin. Ford applies since
`H/2^(j+1)<=sqrt(HY/2^j)`. The logarithms are comparable to `log H`, and `sum 2^(-j)<=2`. The remaining `k<<sqrt H` contribute at most `O(Y sqrt H)` distinct products. This proves (8), including the rectangular normalization.

## 3. Proof of the cut theorem, including the frequency range

Let
\[
 g(n)=\frac1q\sum_{r=1}^q p(rn),\qquad
 M_H(t)=\frac1H\sum_{k\le H}k^{it}.
\]
Then `g` is even and `q`-periodic, with `|g|<=1`. Partial summation of the mean-zero periodic function `p(kn)-g(n)` gives, uniformly in `n`,
\[
 A_HF(n)=M_H(t)n^{it}g(n)
       +O\!\left(\frac{q(1+|t|\log H)}H\right).           \tag{9}
\]
The elementary sum–integral comparison also gives
\[
 |M_H(t)|\ll (1+|t|)^{-1}+(1+|t|\log H)/H.                \tag{10}
\]

For `w(n)=n^(it)g(n)` and `v=A_HG`, discrete summation by parts expresses their current as
\[
 \frac1X\sum_{n\le Y} n^{it}h(n)v(n)
 +O((1+|t|\log(2X))/X),\qquad
 h(n)=g(n-1)-g(n+1).                                     \tag{11}
\]
Here `h` is odd and `q`-periodic, with norm at most two. The endpoint terms are `O(1/X)`; the remaining error is bounded using
`sum_{n=2}^X log((n+1)/(n-1))<=2 log(X+1)`.
The sum in (11) is exactly `(XH)^(-1) sum_a G(a) S_{h,t}(a)`. Thus (6), not a global spectral estimate, controls it against every bounded `G`.

If `q sigma<=1`, choose `U=(q sigma)^(-1/3)`. Since `sigma>=1/H`,
`1<=U<=H^(1/3)<sqrt H`.

* For `|t|<=U`, (6), (9), and (11) give
  `O((q sigma)^(1/3)+q log(H)/sqrt(H)+H^(1/3) log(2X)/X)`.
* For `U<|t|<sqrt H`, (9)–(10) give the stronger pointwise estimate
  `||A_HF||_infty << 1/U+q log(H)/sqrt(H)`.
* For `sqrt H<=|t|<=T_H`, the following derivative argument gives
  `||A_HF||_infty << E_H`.

If `q sigma>1`, the trivial cut bound two already suffices for (2).

**Uniform high-frequency argument.** Discard an initial segment of length `O(sqrt H)`, at normalized cost `O(H^(-1/2))`, so that the remainder is a union of full descending dyadic intervals `(L,2L]` with `L>=sqrt H/2`. Split each interval into its `q` residue classes. After parametrizing a class, its length is comparable to `K=L/q`, with `K>=H^(1/4)` for large `H`. The classical derivative estimate of order `r>=2`, applied to `(t/(2pi)) log(r_0+qj)`, gives its normalized sum the bound
\[
 \ll (|t|/K^r)^{a_r}
       +K^{-b_r}(|t|/K^r)^{-a_r},\qquad
 a_r=(2^r-2)^{-1},\quad b_r=2^{2-r}.                      \tag{12}
\]
This version has a constant uniform in `r`: the cited derivative theorem has a constant independent of the order, its derivative-size-ratio factor is `A^(b_r)`, and here `A<=6^r`. The extra factors `((r-1)!/(2pi 3^r))^(+/-a_r)` are uniformly bounded as well. This is why increasing the order below is legitimate.

Choose `r=floor(log|t|/log K)+2`. If `r>=3`, then
`K^(-2)<=|t|/K^r<K^(-1)` and `b_r>=3a_r`, so (12) is `O(K^(-a_r))`. If `r=2`, it is
`O(sqrt(|t|)/K+|t|^(-1/2))=O(H^(-1/8))` because `|t|<K` and `|t|>=sqrt H`.
In the stated frequency range,
\[
 r\le R:=\left\lceil\frac{\log\log H}{2\log2}\right\rceil+3,
 \qquad 2^R\le16\sqrt{\log H}.
\]
Hence `K^(-a_r)<=exp(-sqrt(log H)/64)=E_H`. Summing over residue classes and dyadic intervals retains this **normalized** bound: their lengths sum to at most `H`. This proves the last bullet and (2).

For (4), use the same high-frequency argument with `q=1`. Below `sqrt H`, apply discrete summation by parts directly to `M_H(t)n^(it)`, whose total variation on `[1,Y]` is at most `|t| log Y`; there is no odd-periodic term to estimate.

## 4. A quantitative approximation inverse with the right weights

Let `P(m)=sum_j c_j p_j(m)m^(it_j)`, where `|p_j|<=1`, each period is at most `Q<=H^(1/6)`, and `|t_j|<=T_H`. Write `W(P)=sum_j |c_j|`, and let `epsilon(X,H,Q)` denote the right side of (2), with `q` replaced by `Q`, times its absolute constant. Bilinearity and the one-label theorem imply
\[
 |C(P,G)|\le W(P)\epsilon(X,H,Q)\qquad(|G|\le1).
\]
For **any** bounded label `F`, without assuming `P` is bounded,
\[
 \boxed{\quad
 \sup_{|G|\le1}|C(F,G)|\le
 \inf_P\left\{\frac{2Y}{X}\|F-P\|_{L^1(\mu)}
                    +W(P)\epsilon(X,H,Q)\right\}.\quad}  \tag{13}
\]
Indeed, each row error occurs at most twice in the current, and
`sum_{n<=Y} A_H|F-P|(n)=Y ||F-P||_(L1(mu))`. Counting-measure approximation is not substituted for this incidence-weighted statement.

For example, fix `0<=beta<gamma`, put `Q=floor((log H)^beta)` and
`W_0=(log H)^((gamma-beta)/6)`. At polynomial `H`, `W_0 epsilon ->0`. If `|C(F,G)|>=c>0`, then, for large `X`, **both** labels have incidence `L1` distance at least `cX/(4Y)` from every such model with `W(P)<=W_0`.

This is a genuine necessary condition on a bounded-cut witness. It does **not** say every bounded label has a low-variation Mellin expansion. The missing general inverse/decomposition is exactly where arbitrary rough-core labels and high-complexity superpositions can escape (13).

An exact residual estimate can now be specified. With the preceding `Q,W_0`, let `R_c(X,H)` be the labels `|F|<=1` whose incidence `L1` distance from all these models is at least `c/8`. It remains sufficient to prove, for every `c>0`,
\[
 \limsup_{\delta\downarrow0}\limsup_{X\to\infty}
 \sup_{F,G\in R_c(X,\lfloor X^\delta\rfloor)}|C(F,G)|\le c. \tag{13a}
\]
If either label is outside `R_c`, (13) already bounds its current by `c/2+o(1)`. Conversely the full target would imply (13a). No estimate on this escaping bounded-label class is proved here.

## 5. Exact residuals; no counterexample supplied

For phases `z_p` on primes `p<=N`, let
`chi_z(m)=prod_p z_p^(v_p(m))`, and set `M_H(z)=H^(-1) sum_{k<=H} chi_z(k)`.
The actual bounded labels `F=Re chi_z`, `G=Im chi_z` satisfy the exact identity
\[
 C(F,G)=|M_H(z)|^2\Im\frac1X\sum_{n\le X}
                  \overline{\chi_z(n)}\chi_z(n+1).         \tag{14}
\]
Thus even the following necessary subproblem is still unproved here:
\[
 \lim_{\delta\downarrow0}\limsup_X
 \sup_{|z_p|=1,\ p>H}
 \left|\Im\frac1X\sum_{n\le X}
       \prod_{p>H}z_p^{v_p(n+1)-v_p(n)}\right|=0,
 \qquad H=\lfloor X^\delta\rfloor.                       \tag{15}
\]
This restricts to `z_p=1` for `p<=H`, so `M_H(z)=1` exactly. A positive constant surviving as `delta` tends to zero would already give a genuine bounded-label counterexample; a positive limsup at just one fixed `delta` would refute only the stronger fixed-`delta` assertion. Neither is constructed. Constant current forces positive incidence mass, since `|C(F,G)|<=2Y/X min(||F||_(L1(mu)),||G||_(L1(mu)))`. Thus (15) asks for a genuine bounded-mass phenomenon, not a thin spectral witness.

Very large ordinary Mellin frequencies really contain this subproblem. For each **fixed** finite `N`, unique factorization implies rational independence of the prime logarithms. The continuous orbit `(p^(it))_(p<=N)` is dense in the prime torus, and every tail of that orbit is dense. Consequently every `chi_z` on `[1,N]` can be uniformly approximated by `m^(it)` at arbitrarily large `t`. In particular, the supremum of the sine/cosine current over any unbounded frequency tail equals the supremum in (14) over the finite prime torus. This uses no recurrence bound uniform in growing `N`, and makes no claim that a realizing `t` is comparable to `X`. Equations (2) and (4) force any positive-current realization outside `[-T_H,T_H]` eventually.

The larger arbitrary-core residual retains the exact weights as follows. Let `c_H(n)` remove all prime powers with prime at most `H`; let `s,t` below denote `H`-smooth integers. Put
\[
 w_{X,H}(q,r)=\#\{(s,t):sq\le X,\ sq+1=tr\},
 \quad q,r\text{ are }H\text{-rough},
\]
\[
 \nu_{X,H}(q)=\frac1Y\#\{n\le Y:c_H(n)=q\}.
\]
For labels `F(m)=a(c_H(m))`, `G(m)=b(c_H(m))`,
\[
 C(F,G)=\frac1X\sum_{q,r}w_{X,H}(q,r)
                [a(q)b(r)-b(q)a(r)],\qquad
 \|F\|_{L^1(\mu)}=\sum_q\nu_{X,H}(q)|a(q)|.               \tag{16}
\]
These follow from `c_H(kn)=c_H(n)` for **every** `k<=H`. There is no claim that arbitrary `a,b` in (16) are covered by (13), or that general bounded labels reduce to characters. In particular, a low-frequency function of `log c_H(m)` is not necessarily a low-frequency Mellin function of `log m`.

**Remaining obligation.** A large cut must escape the explicit approximation class in (13); control of that escaping class is not obtained. Already (15), and more generally the bounded weighted core cut (16), remain. The full obligation is still the stated double-limit bounded cut for `D/(XH^2)`, not an average of currents at scales `X/p`. The established LPF stability and near-diagonal nonconcentration would turn that full estimate into the arithmetic target; none of (2)–(16) supplies the missing estimate for all labels.

## 6. Verification and external inputs

* The signed-divisor identity (7) is an exact gcd parametrization, retaining the diagonal and both orientations. Its proof and (11) explicitly retain the `X+1` endpoint. Equations (6), (13), and (16) use the actual incidence weights.
* Ford's input was checked in `/corpus/src/math_0607473/hxy2y.tex:26–36` (also `/corpus/src/math_0401223/hxyz_aom_final.tex:829–832`). Only its stated divisor-interval upper bound is used, with the rectangular deduction supplied above.
* The derivative theorem, including independence of its constant from the derivative order, was checked in `/corpus/src/1601.04493/1601.04493.tex:16–27`. The order, residue-class length, derivative-size ratio, factorial factors, and frequency cutoff needed here are audited explicitly in (12).
* All asymptotic claims above rest on these proofs, not numerical experiments. No finite-field wraparound, fixed-determinant estimate, or untrimmed spectral assertion is invoked.
* `Submission/Spec.lean` has SHA-256 `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`, unchanged from before this investigation. No admitted statement from it is used.

## Independent continuation audit

The main assistant independently checked the exact gcd parametrization in (7), the mean-zero property of `h(bv)` even when b is not coprime to q, Möbius inversion and convergence of the two divisor series, the rectangular Ford decomposition, and the endpoint summation by parts in (11). The Ford hypothesis was read directly in `math_0607473/hxy2y.tex:26--36`. The uniform derivative theorem had also been read directly; the new application retains its order dependence correctly: the ratio factor is at most `(6^r)^(2^(2-r))`, and the factorial/scale factors raised to `+/-1/(2^r-2)` remain bounded. The inequalities `K>=H^(1/4)`, `r<=R`, and `2^R<=16 sqrt(log H)` give the stated exponential saving. The low/middle-frequency balancing and the incidence-weighted approximation bound were checked separately. These establish only the stated controlled label class. There is still no inverse theorem placing arbitrary bounded labels, or the actual LPF labels, in that class with the required coefficient budget; (13a), (15), and the full target remain unproved.
