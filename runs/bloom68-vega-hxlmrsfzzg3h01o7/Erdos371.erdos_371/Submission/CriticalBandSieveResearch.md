# Critical-band positive sieve: independent analytic audit

## Verdict

**The proposed positive-envelope bounds are valid, with the conventions and uniformity qualifications below.** In particular, the both-prime sector is `O(X/log X)`, and every sector with both `Omega(d)` and `Omega(v)` bounded by fixed constants is `o(X)`. These are upper bounds for the **actual positive envelope**, not a replacement of the prime weight by a sieve surrogate. They do not give cancellation in the unrestricted signed Type II functional, the covariance estimate (SC), the pilot, or the largest-prime-factor density theorem.

The substantive points checked here are the uniform two-linear-form sieve, the independent dimension-at-most-three Selberg sieve in two integer variables, its accumulated remainder, and the singular-factor averages. Two useful sharpenings are:

* The prime-`d`, unrestricted-`v` positive envelope is `O(X)`, improving the `O(X log X)` coefficientwise bound recorded in DirectOddCountResearch §13.3, but still not giving `o(X)`.
* In the box argument, with `tau=1/20-epsilon-gamma>0`, the proposed condition `kappa<tau/4` is sufficient; the displayed remainder actually permits any fixed `kappa<tau/2`.

Qualifications: a “raw/unweighted count” below retains the kernel's `b`-weight and removes the arithmetic coefficient weights; logarithms of roughness thresholds are padded at small thresholds; the nontrivial stretched-exponential example has `0<nu<1/2`. No Spec or pre-existing research file is edited. This is an analytic research proof using the classical inputs identified in §7, not a Lean formalization.

## 1. Functional, normalization, and the entire tail

Put
\[
 L=\log X,\qquad P=X^{3/5},\quad D=V=X^{9/20},\quad
 Q=DV=X^{9/10},\quad B=X^{1/10},\quad H=X^{1/2}.
\]
Thus `BQ=X` and `P/B=H`. All implied constants may depend on the fixed smooth cutoffs and the indicated fixed positive exponent margins. The block has `p~P` prime, `d~D`, `v~V`; cutoffs bounded by one may be suppressed in positive upper bounds. As in DirectOddCountResearch §§11–13,
\[
 b_z(v)=\sum_{e\mid v,\ e>z}\Lambda(e),\qquad
 0\le b_z(v)\le\log v.
\]
Only §6.4 needs the particular choice `z=X^(7/50)`.

The critical Poisson expression is
\[
 R_E=\sum_{(d,v)\in E}\mu(d)b_z(v)
 \sum_{p\sim P}\log p\sum_{b\ge1}
 W_*(p/P,dv/Q,b/B)
 \bigl(1_{p\mid bdv-1}-1_{p\mid bdv+1}\bigr).             \tag{1}
\]
The kernel is real odd in its last variable and uniformly Schwartz on the relevant compact set in its first two variables. Consequently, for every fixed `J`,
\[
 |W_*(r,t,x)|\ll_J\psi_J(x):=x(1+x)^{-J-1}\quad(x>0).  \tag{2}
\]
The linear behavior at zero follows from oddness and a bounded first derivative. There is **no remaining factor of H**: in (12.3) of the prior note, `T=H` makes `T/(2iH)=1/(2i)`, and the Fourier argument is `-Hb/p=-(b/B)/(p/P)`. Combining positive and negative `b` gives exactly the difference in (1).

Write `mathcal E(E)` for the positive envelope of (1): replace `mu(d)` by `mu(d)^2=|mu(d)|`, `W_*` by `|W_*|`, and the indicator difference by the sum. Thus `|R_E|<=mathcal E(E)`. The *raw* envelope removes `mu(d)^2`, `b_z(v)`, and `log p`, but retains the same kernel and indicators. A literal unweighted sum over every positive `b` is not the count being bounded.

Fix `epsilon>0`. Before any cofactor decomposition, truncate to
\[
 b\le B X^\epsilon.                                    \tag{3}
\]
Indeed, for either sign and every fixed `b,d,v`,
\[
 \sum_{p\sim P,\ p\mid bdv\pm1}\log p
 \le\log|bdv\pm1|\ll\log(2bQ).
\]
The neighbors are nonzero. For `J>1`, summing the whole tail, rather than replacing its logarithm pointwise by `O(L)`, gives
\[
 \sum_{b>BX^\epsilon}\psi_J(b/B)\log(2bQ)
 \ll_{J,\epsilon}B X^{-(J-1)\epsilon}L.
\]
There are `O(Q)` pairs and `b_z(v)<<L`. Hence the envelope tail is
\[
 \ll X L^2 X^{-(J-1)\epsilon}.                          \tag{4}
\]
For any prescribed `A>0`, choose a sufficiently large Schwartz order `J` to make this `O_A(X^{-A})`. For the raw tail, use `# {p~P : p|bdv+/-1} <= log(2bQ)/log P`; the same calculation gives `O(X X^(-(J-1)epsilon))`, also arbitrarily power-small. All subsequent bounds include this tail by absorption. Positivity makes them valid for any subset of the specified arithmetic sector.

## 2. Singular-factor averages

Define
\[
 f(n)=\prod_{\substack{q\mid n\\q>2,\ q\ {\rm prime}}}
       {q-1\over q-2},\qquad f(1)=1.
\]
Here and below products ignore multiplicity. Equivalently,
\[
 f(n)=\sum_{e\mid n}h_0(e),\qquad
 h_0(q)={1\over q-2}\ (q>2),
\]
where `h_0(1)=1` and `h_0` is supported on odd squarefree integers and is multiplicative there. Since
\[
 \sum_{e\ge1}{h_0(e)\over e}
 =\prod_{q>2}\left(1+{1\over q(q-2)}\right)<\infty,
\]
counting multiples proves, without a pointwise divisor bound,
\[
 \sum_{n\le T}f(n)\ll T,\quad
 \sum_{n\le T}{f(n)\over n}\ll1+\log T,\quad
 \sum_{n\asymp T}{f(n)\over n}\ll1.                    \tag{5}
\]
Also `f(uv)<=f(u)f(v)`. Dyadic summation and (2), (5) give
\[
 \sum_{b\ge1}\psi_J(b/B)f(b)\ll_J B\qquad(J>1).         \tag{6}
\]
Finally, for primes in a large dyadic interval,
\[
 \sum_{q\sim T,\ q\ {\rm prime}}{f(q)\over q}
 \ll {1\over\log T},                                  \tag{7}
\]
by Chebyshev's bound and `f(q)=1+O(1/q)`.

## 3. Both-prime count: an independent one-variable proof

From now on choose `0<epsilon<1/20`; this is our freely chosen tail-truncation margin. For either sign, write the divisibility condition as
\[
 bdv-ap=\sigma,\qquad\sigma\in\{-1,1\},\qquad
 a\asymp A_b:={bQ\over P}.                             \tag{8}
\]
The `a` range has a fixed ratio of upper to lower endpoints, so covering it dyadically costs only a fixed number of pieces, not `log X`. In particular, `A_b>=X^(3/10)` and, after (3), `a<<X^(2/5+epsilon)`.

Fix `a,b` and a prime `d~D`, and put `M=bd`. If `(a,M)>1`, (8) is impossible. Otherwise all solutions have
\[
 p=p_0+Mt,\qquad v=v_0+at,\qquad Mv_0-ap_0=\sigma.
\]
Both forms are primitive. The permitted `t` values lie in an interval of length at most `P/M`; enlarging and translating it to an interval of integer length `N=O(P/M+1)` is legitimate. For the sieve we can choose
\[
 N\asymp {P\over bd}\gg X^{1/20-\epsilon}.             \tag{9}
\]
For a prime `q`, the number of forbidden roots of the product of the two forms is
\[
 \nu(q)=\begin{cases}1,&q\mid aM,\\2,&q\nmid aM.\end{cases}
\]
If `aM` is odd, parity makes the count zero: both counted primes exceed two. Otherwise the singular series is exactly
\[
 2C_2 f(aM),\qquad
 C_2=\prod_{q>2}\left(1-{1\over(q-1)^2}\right).          \tag{10}
\]
This is a sieve of **two linear forms**, of sieve dimension two, not the dimension-one “linear sieve.”

The uniformity hypothesis in Ford–Konyagin–Luca's lemma (source in §7) is satisfied. All coefficients here have polynomial height in `X`; in particular `aM<=X^C` for a fixed `C`. Splitting at `q=L` gives
\[
 \sum_{q\mid aM}{\log q\over q}
 \le \sum_{q\le L}{\log q\over q}
       +{\log(aM)\over L}
 \ll\log L=o(\log N).                                 \tag{11}
\]
For the first term Chebyshev and partial summation suffice. The determinant remains `sigma` when the interval is translated, so translating introduces no new exceptional primes. The cited uniform lemma, with `k=2`, therefore bounds the number of prime pairs `(p,v)` by
\[
 \ll {P\over bd L^2} f(abd).                           \tag{12}
\]
Only the length of the containing interval, not a lower bound for the length of the actual intersection, is required.

Summing (12), using (5)–(7) and `f(abd)<=f(a)f(b)f(d)`, gives the raw envelope
\[
 \begin{aligned}
 &\ll {P\over L^2}\sum_b{\psi_J(b/B)f(b)\over b}
      \sum_{d\sim D\ {\rm prime}}{f(d)\over d}
      \sum_{a\asymp A_b}f(a)\\
 &\ll {P\over L^3}\sum_b\psi_J(b/B)f(b){A_b\over b}
 \ll {BQ\over L^3}={X\over L^3}.
 \end{aligned}                                      \tag{13}
\]
The factor `A_b=bQ/P` cancels the denominator `b`. Restoring `log p` and `b_z(v)<=log v` costs `O(L^2)`, proving
\[
 \boxed{\mathcal E(d,v\ {\rm both\ prime})\ll X/L.}     \tag{14}
\]
For the specified `z`, `b_z(v)=log v` on this prime sector, though equality is unnecessary for the upper bound.

### Prime residuals with small cofactors

Let `d=r ell'`, `v=s ell`, with both `ell',ell` prime and `r,s<=X^gamma`, where `epsilon+gamma<1/20`. For fixed `a,b,r,s,ell'`, the two prime forms now come from
\[
 (brs\ell')\ell-ap=\sigma.
\]
Their interval length is comparable to `P/(bds)`, at least a constant times `X^(1/20-epsilon-gamma)`. Moreover, `ell'~D/r`, so (7) supplies `1/log(D/r)<<_gamma 1/L`. The same proof gives, for each fixed `r,s`,
\[
 \mathcal E_{r,s}({\rm prime,prime})
 \ll {X\over L}{\mu^2(r)f(r)f(s)\over rs}.             \tag{15}
\]
We used only `mu^2(r ell')<=mu^2(r)` and `b_z(s ell)<=log(s ell)`; no unjustified coprimality or identity for `b_z` is needed. Thus any sector admitting such factorizations with `r<=Y_d`, `s<=Y_v`, where `Y_d,Y_v<=X^gamma`, satisfies
\[
 \mathcal E\ll {X\over L}
 \left(\sum_{r\le Y_d}{\mu^2(r)f(r)\over r}\right)
 \left(\sum_{s\le Y_v}{f(s)\over s}\right)
 \ll {X(1+\log Y_d)(1+\log Y_v)\over L}.               \tag{16}
\]
Multiple representations only overcount a positive quantity.

## 4. Uniform two-parameter rough-number sieve

Here is a self-contained proof of the stronger claim; it is not inferred from the dimension-one application in Browning–Heath-Brown.

Fix `epsilon,gamma>=0`, with `epsilon>0` and
\[
 \tau={1\over20}-\epsilon-\gamma>0,
 \qquad 1\le r,s\le X^\gamma,
 \qquad \xi=X^\kappa.
\]
The proposed `0<kappa<tau/4` is safe. The proof below in fact only needs `0<kappa<tau/2`, with a fixed strict margin. Set
\[
 y_i'=\min(y_i,\xi),\quad y_i\ge1,\qquad
 \ell(t)=\max\{1,\log t\}.
\]
A threshold `y_i=1` means that no roughness restriction is imposed. Let `mathcal E_{r,s}(y_1,y_2)` denote the envelope restricted to `d=rm`, `v=sn`, with `P^-(m)>y_1` and `P^-(n)>y_2`. The usual convention is `P^-(1)=infinity`; in this block `m,n` are in fact large.

We prove the uniform bound
\[
 \boxed{
 \mathcal E_{r,s}(y_1,y_2)
 \ll {X L^2\over\log\xi\,\ell(y_1')\ell(y_2')}
       {\mu^2(r)f(r)f(s)\over rs}
 \ll {X L\over\ell(y_1')\ell(y_2')}
       {\mu^2(r)f(r)f(s)\over rs}.}                    \tag{17}
\]
Constants in the second bound can depend on `kappa`. The first bound records the sieve scale explicitly.

### 4.1 Residue boxes and polynomial identity

Put `c=brs`. For fixed `a~A_b`, the equation is
\[
 cmn-ap=\sigma.
\]
It is empty unless `(a,c)=1`. Otherwise there are exactly `phi(a)` pairs of units `(m_0,n_0)` modulo `a` satisfying `cm_0n_0= sigma (mod a)`: each unit `m_0` determines one unit `n_0`. In such a pair write
\[
 m=m_0+au,\quad n=n_0+aw,
\]
\[
 F(u,w):=p=ca\,uw+cn_0u+cm_0w+p_0,
 \qquad p_0={cm_0n_0-\sigma\over a}\in\mathbb Z.         \tag{18}
\]
The exact identity `aF=cmn-sigma` is useful also at primes dividing `a`. The `u,w` intervals have lengths
\[
 T_1={D\over ra},\quad T_2={V\over sa},\qquad
 \min(T_1,T_2)\gg X^\tau.                              \tag{19}
\]
For an upper bound drop the additional condition `F~P` and sieve on the enclosing rectangle. Every originally counted prime `p` exceeds `xi`, so it survives all of the imposed prime-`F` tests. Conditions on the smooth weights have already been bounded by (2).

### 4.2 Exact local densities

At each **odd** prime `q<=xi`, forbid `F=0 (mod q)` and, additionally, `m=0` if `q<=y_1'`, and `n=0` if `q<=y_2'`. Let `j` be the number of the latter two tests and `rho(q)` the number of forbidden pairs modulo `q`. The survival proportions are:

| Prime | `j=0` | `j=1` | `j=2` |
|---|---:|---:|---:|
| `q` does not divide `ac` | `1-1/q+1/q^2` | `(1-1/q)^2` | `(1-1/q)(1-2/q)` |
| `q` divides `c` | `1` | `1-1/q` | `(1-1/q)^2` |
| `q` divides `a` | `1-1/q` | `1-1/q` | `1-1/q` |

To verify the first row, change coordinates to `m,n` modulo `q`. The `F=0` locus is the nonzero hyperbola `mn=sigma/c`, with `q-1` points; the selected coordinate axes have `j q-1_(j=2)` points and are disjoint from it. If `q|c`, `F=-sigma/a` is a nonzero constant. If `q|a`, `m,n` are fixed units, and `F` is a nonconstant affine-linear polynomial in `u,w`, with both linear coefficients nonzero, hence exactly `q` zeros.

At `q=2`, the generic `j=2` case is a full obstruction, and the target is empty. One may otherwise handle parity explicitly; for a uniform upper bound we simply **omit 2 throughout the sieve**. This enlarges the sifted set and avoids dividing by a zero local survival factor. No assertion that a zero factor can be replaced multiplicatively by a constant is needed.

For the remaining primes,
\[
 g(q):={\rho(q)\over q^2}<1,\qquad
 \rho(q)\le3q,\qquad (1-g(q))^{-1}\le9/2<5.            \tag{20}
\]
Primes with `g(q)=0` may be omitted. CRT and elementary rectangle counting give, for every squarefree product `k` of the sieve primes,
\[
 A_k=T_1T_2 g(k)+R_k,\qquad
 |R_k|\ll3^{\omega(k)}(T_1+T_2+k).                     \tag{21}
\]
Indeed there are `rho(k)<=3^omega(k) k` bad residue pairs modulo `k`, and each contains `T_1T_2/k^2+O((T_1+T_2)/k+1)` points. This is uniform in all coefficients and in the chosen residue pair.

### 4.3 Selberg weights and the accumulated error

Let `mathcal P` be the product of the active odd primes at most `xi`, and define
\[
 \eta(k)=\prod_{q\mid k}{g(q)\over1-g(q)},\qquad
 G(\xi)=\sum_{\substack{k\le\xi\\k\mid\mathcal P}}\eta(k),
 \qquad \mathcal V(t)=\prod_{\substack{q\le t\\q\mid\mathcal P}}(1-g(q)).
\]
The Selberg quadratic form with squarefree support `d<=xi`, `d|mathcal P`, has minimum
\[
 \sum_{d,e}\lambda_d\lambda_e g([d,e])={1\over G(\xi)},
 \qquad\lambda_1=1.
\]
For completeness, its diagonalization follows from
\[
 g([d,e])=g(d)g(e)\sum_{k\mid(d,e)}\eta(k)^{-1}.
\]
Writing `z_k=sum_(k|d) lambda_d g(d)`, Möbius inversion gives `lambda_1=sum_k mu(k)z_k`. Cauchy gives the minimum `1/G`, attained at `z_k=mu(k)eta(k)/G`. Inverting again gives the explicit minimizing weights
\[
 \lambda_d={\mu(d)\over G(\xi)}
       \prod_{q\mid d}(1-g(q))^{-1}
       \sum_{\substack{k\le\xi/d\\k\mid\mathcal P\\(k,d)=1}}\eta(k),
 \qquad |\lambda_d|\le5^{\omega(d)}.                  \tag{22}
\]
All inverses here are for active primes, with `g(q)>0`.

The square of the divisor sum is a nonnegative majorant of the sifted indicator. Grouping its errors by `k=[d,e]<=xi^2`, the absolute coefficient is at most `35^omega(k)`: a prime can occur only in `d`, only in `e`, or in both, with respective bounds `5,5,25`. Equations (21)–(22) therefore give
\[
 S\le {T_1T_2\over G(\xi)}
 +O\left(\sum_{k\le\xi^2}105^{\omega(k)}(T_1+T_2+k)\right)
\]
\[
 \hspace{12mm}\le {T_1T_2\over G(\xi)}
 +O\left((\log(2\xi))^{104}
       [\xi^2(T_1+T_2)+\xi^4]\right).                 \tag{23}
\]
The divisor-sum estimate follows, for example, from `105^omega(k)<=tau_105(k)`.

Here is the promised **uniform** comparison `G(xi)>>1/mathcal V(xi)`, without invoking a dimension-three asymptotic. Take a sufficiently small fixed `theta>0` and expand the full Euler product on primes at most `xi^theta`. Normalize the weight `eta(d)` on all its divisors to a probability measure. The probability that `q|d` is `g(q)`, so
\[
 \mathbb E\log d=\sum_{q\le\xi^\theta}g(q)\log q
 \le3\sum_{q\le\xi^\theta}{\log q\over q}
 \ll\theta\log\xi.
\]
Choose `theta` so this is at most `(log xi)/2`. Markov's inequality places at least half of the total divisor weight on `d<=xi`. Thus
\[
 G(\xi)\ge\tfrac12\mathcal V(\xi^\theta)^{-1}.
\]
Moreover, (20) and the prime harmonic estimate imply
\[
 \log{\mathcal V(\xi^\theta)\over\mathcal V(\xi)}
 \le3\sum_{\xi^\theta<q\le\xi}{1\over q}+O(1)
 \ll_\theta1.
\]
This proves the comparison, uniformly in `a,c,y_1,y_2` and the residue pair.

Every odd-prime survival in the table is at least `(1-1/q)(1-2/q)`. Mertens' theorem and the convergent twin-prime product therefore give
\[
 \mathcal V(\xi)\gg(\log\xi)^{-3}.                    \tag{24}
\]
The error in (23), divided by `T_1T_2`, is
\[
 \ll L^{104}\bigl(X^{2\kappa-\tau}+X^{4\kappa-2\tau}\bigr)
 =o(L^{-3})\qquad(2\kappa<\tau).                      \tag{25}
\]
Consequently, for each individual residue box,
\[
 S\ll T_1T_2\mathcal V(\xi).                           \tag{26}
\]
The error has been absorbed **uniformly per box**, so summing over all `phi(a)` boxes and all parameters introduces no unaccounted total-error factor.

## 5. Product bound and summation of the boxes

Put
\[
 A_*(a)=\prod_{\substack{q\mid a\\q>2}}{q\over q-2}.
\]
Compare the table with `(1-1/q)^(1+j)`. At generic primes the ratio is `1+1/(q(q-1))` for `j=0`, equals one for `j=1`, and is less than one for `j=2`. The product of all the upward generic corrections is bounded. If `q|c`, the ratio is `q/(q-1)<=f(q)`. If `q|a`, it is `(1-1/q)^(-j)<=q/(q-2)`. Mertens' theorem, with a constant for thresholds below three, now proves
\[
 \mathcal V(\xi)\ll
 {A_*(a)f(c)\over\log\xi\,\ell(y_1')\ell(y_2')}.       \tag{27}
\]
Factors belonging to primes larger than `xi` on the right only enlarge it.

Multiplying (26) by `phi(a)` and summing (27) over `a~A_b` is safe because
\[
 {\varphi(a)A_*(a)\over a^2}
 =\begin{cases}f(a)/a,&a\text{ odd},\\ f(a)/(2a),&a\text{ even},\end{cases}
 \qquad
 \sum_{a\asymp A_b}{\varphi(a)A_*(a)\over a^2}\ll1.    \tag{28}
\]
In particular, a worst-case pointwise bound for `A_*(a)` must not be inserted before averaging. Since `T_1T_2=Q/(rs a^2)` and `f(c)<=f(b)f(r)f(s)`, the total raw count for fixed `r,s` is at most
\[
 {Q f(r)f(s)\over rs\log\xi\,\ell(y_1')\ell(y_2')}
 \sum_b\psi_J(b/B)f(b)
 \ll {X f(r)f(s)\over rs\log\xi\,\ell(y_1')\ell(y_2')}.
                                                               \tag{29}
\]
Restoring the actual coefficients uses precisely
\[
 |\mu(rm)|=\mu^2(rm)\le\mu^2(r),\qquad
 b_z(sn)\le\log(sn)\ll L,\qquad \log p\ll L.
\]
This proves (17). Neither independence of the arithmetic coefficients nor a pointwise Möbius estimate was used.

## 6. Consequences and bounded numbers of prime factors

### 6.1 Unrestricted and power-rough sectors

Take `r=s=1` in (17). With no roughness restriction the envelope is
\[
 \mathcal E(\text{whole balanced block})\ll XL.          \tag{30}
\]
If both `d,v` are `X^delta`-rough, for fixed `delta>0`, the two padded logarithms are comparable to `L` (or the sector is empty), giving
\[
 \mathcal E(P^-(d),P^-(v)>X^\delta)\ll_\delta X/L.       \tag{31}
\]
The constants can depend on the fixed sieve exponent margins as well. Taking both variables prime gives the raw `X/L^3` and weighted `X/L` bounds again.

### 6.2 Stretched-exponential roughness

For fixed `0<nu<1/2`, let `y=exp(L^(1/2+nu))`. Eventually `y<xi`, so
\[
 \mathcal E(P^-(d),P^-(v)>y)
 \ll {XL\over(\log y)^2}={X\over L^{2\nu}}=o(X).       \tag{32}
\]
At `nu=0` this method gives only `O(X)`. At `nu>=1/2` the specified `d,v` rough sector is empty for sufficiently large `X`, since `y` already exceeds the block sizes; it is not the same nontrivial logarithmic regime.

### 6.3 A prime and a rough variable

If `d` is prime, it survives sieving to `xi`; put `y_1=xi`, `y_2=y`. Then
\[
 \mathcal E(d\ {\rm prime},\ P^-(v)>y)
 \ll {X\over\ell(\min(y,\xi))}.                        \tag{33}
\]
For `y>=2` the usual expression with `log min(y,xi)` is equivalent. In particular, the bound is `o(X)` for any `y=y(X)` tending to infinity. With unrestricted `v` it gives `O(X)`, not `o(X)`. The analogous prime-`v` statement follows from the same positive estimate; no symmetry assertion about the signed coefficients is necessary.

### 6.4 Fixed `Omega(d)<=K`, `Omega(v)<=M`

Here `Omega` counts prime factors **with multiplicity**. Let `K,M>=1` be fixed. Choose fixed `epsilon,gamma,delta>0` such that
\[
 \epsilon+\gamma<1/20,\qquad \gamma<7/50,\qquad
 \delta\max(K,M)\le\gamma,
\]
and put `y=X^delta`, `z=X^(7/50)`. Factor canonically
\[
 d=rm,\qquad v=sn,
\]
where `r,s` are the **full prime-power parts supported on primes at most y**, and `m,n` have no prime divisor at most `y`. Then `r,s<=X^gamma`, and `(r,m)=(s,n)=1`.

Both residuals exceed one: if, for example, `m=1`, then `d<=y^K<=X^gamma`, contradicting `d~X^(9/20)`. Hence
\[
 \Omega(r)\le K-1,\qquad\Omega(s)\le M-1.              \tag{34}
\]
Nonzero `mu(d)` also makes `r` squarefree. Because `s<z` for large `X`, and a prime-power divisor of the coprime product `sn` divides either `s` or `n`, one has the **valid identity and bound**
\[
 b_z(sn)=b_z(n)\le\log n.                              \tag{35}
\]
The last inequality is generally **not an equality**: being `y`-rough does not mean that `n` has no prime-power divisor at most `z`.

For fixed `k>=0`, the required cofactor harmonic sums satisfy
\[
 \sum_{\substack{P^+(t)\le y\\\Omega(t)\le k}}{f(t)\over t}
 \ll_k(1+\log\log X)^k.                                \tag{36}
\]
To see this, `f(q^e)=f(q)<=f(q)^e`, and for each `j` the expansion of `(sum_(q<=y) f(q)/q)^j` majorizes the sum for `Omega(t)=j`. Also `sum_(q<=y) f(q)/q=log log y+O(1)`. The convention includes `t=1`. An extra `mu^2(t)` only decreases the sum.

Apply (17) to every canonical pair `r,s`, taking `y_1=y_2=y`. Both sieve logarithms are fixed positive multiples of `L`. Dropping the remaining restrictions on `m,n` only enlarges the positive count. Equations (34)–(36) give
\[
 \boxed{
 \mathcal E(\Omega(d)\le K,\Omega(v)\le M)
 \ll_{K,M}{X\over L}(1+\log\log X)^{K+M-2}=o(X).}       \tag{37}
\]
The corresponding raw bound is `O_(K,M)(X(1+log log X)^(K+M-2)/L^3)`: apply (29) and (36), now summing over all `r` without `mu^2(r)`. It is not inferred by dividing (37) by `L^2`. If either `K` or `M` is zero, the block is empty. This argument permits repeated primes in `v`; it does not silently replace `Omega` by the number of distinct prime factors.

## 7. Source checks, verification, and exact remaining blockers

**Sources inspected locally.**

* `Submission/DirectOddCountResearch.md:699–709, 718–796, 885–916` supplies the actual coefficient `b_z`, the critical-band setup, and the Poisson normalization. Its §13.3 contains the earlier, weaker prime-`d` envelope bound. The new estimates do not invalidate that upper bound; they improve it.
* Ford, Konyagin and Luca, *Prime chains and Pratt trees*, arXiv:0904.0473, `/corpus/src/0904.0473/chains_short6.tex:868–924`. The lemma explicitly uses the primitive linear forms, root counts, and `sum_q (k-nu(q))log(q)/q`; its uniformity is exactly what (9)–(11) verify. No prime equidistribution asymptotic is used.
* Browning and Heath-Brown, *Counting Rational Points on Quadric Surfaces*, arXiv:1801.00979, `/corpus/src/1801.00979/browning2018.tex:1246–1285`. This passage illustrates Selberg sieving of polynomial values in a box and a summed congruence-count remainder. Its actual application has sieve dimension **one**. It is not a source for the present dimension-three conclusion; §§4–5 above prove the needed version independently.
* Other classical inputs are Chebyshev's bound, Mertens' prime products/prime harmonic estimates, CRT, Möbius inversion, and elementary summation of fixed-order divisor functions. The tails and all coefficient and cofactor estimates have been displayed explicitly.

**Secondary algebraic regression.** `/tmp/critical-band-sieve-check.py` and its log `/tmp/critical-band-sieve-check.log` check the polynomial identity, the exact local-root table (including 2), and exact rational Selberg weights. The run passed 21,168 local-root cases, detected 276 full parity obstructions correctly, and passed five rational quadratic-form/weight checks. These finite checks are not the proof of any asymptotic estimate; that proof is §§1–6.

**What is not proved.**

1. The full signed balanced functional is not `o(X)` by this argument. Its proved positive bound is `O(XL)`. For every fixed `K,M`, (37) removes the bounded-`Omega` sector, but leaves `Omega(d)>K` or `Omega(v)>M`. There is no uniform tail estimate allowing `K,M` to tend to infinity after summing. In the unrestricted cofactor sum, (16) can lose two full factors of `L`; the bounded-`Omega` harmonic estimate is essential, not dispensable.
2. No estimate is supplied for the signed distinct-`d`, distinct-prime covariance `C_(L^6)` in DirectOddCountResearch §13.1. In particular, its sufficient condition `(SC): |C_(L^6)| << X^(31/20)/L^2` is untouched. A first-moment upper bound on selected sectors is not that second-moment statement.
3. Upper sieve bounds cannot be subtracted to manufacture cancellation between `+1` and `-1`, or to discard the composite remainder in a short-divisor prime surrogate. The Möbius signs and the antisymmetric residues have been discarded only for this positive upper-bound purpose.
4. The proof concerns a balanced block and a fixed critical smooth frequency band. It neither assembles all remaining Type II blocks/frequencies of the pilot nor addresses all exponent regions needed for the largest-prime-factor density assertion. No conclusion about the full LPF theorem follows.

**Deliverable:** `Submission/CriticalBandSieveResearch.md`. All results above are unconditional analytic upper bounds with the stated fixed-parameter conventions. No new signed-cancellation or formal theorem is claimed.
