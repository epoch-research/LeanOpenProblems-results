# Residual covariance: obstruction to the tested double-extraction / Type III route

## Outcome (B)

The route tested is **Ramaré extraction in both variables, Cauchy in the two residual variables, then smooth two-dimensional completion**. Its exact off-diagonal transform is a product of two *odd Kloosterman differences*, at the two distinct prime moduli. The four signs annihilate all imprimitive frequencies, but leave conductor `p1 p2`; they do not turn the problem into a prime-modulus Type III sum. Below are the identity, the actual weights, and the numerical failures of the closest checked estimates. Complementary divisor switching also has a genuinely applicable determinant theorem, but its error here is `X^(3/2+epsilon)`, not sublinear.

**No signed `o(X)` bound is proved.** This is an obstruction to these specific applications, not a lower bound for `R`, a no-go theorem for dispersion, or a claim to have exhausted the literature. No new positive-envelope deletion, logarithmically smoothed Möbius weight, scale average, or admitted target is used.

## 1. Exact double Ramaré identity and compatible norm

Throughout,
\[
 P=X^{3/5},\quad D=V=X^{9/20},\quad Q=DV=X^{9/10},
 \quad B=X^{1/10},\quad z=X^{7/50},\quad L=\log X.
\]
Use the functional in DirectOddCountResearch §13.1, with the question's `u(d/D)`, `w(v/V)` and `W(p/P,dv/Q,b/B)`. The cutoffs are fixed smooth compactly supported functions on positive scales; `W` is odd and uniformly Schwartz in its last coordinate, with uniform smooth seminorms on the relevant first-two-coordinate compact set. Complex weights are allowed by putting conjugates in second moments. Set
\[
 b_z(t)=\sum_{e\mid t,\ e>z}\Lambda(e),\qquad
 I=\{r\text{ prime}:L^{12}<r\le X^{1/1000}\}.
\]
The established `o(X)` deletion concerns pairs for which **both** variables have no `I` factor, and the repeated-`I`-factor sector. It does not delete pairs where just one variable has no `I` factor. In this note `R_good` denotes only the subfunctional where **each** of `d,v` has an `I` factor and neither has a repeated `I` factor. The two singly factor-bearing branches remain outside this double-extraction calculation. No assertion that this subfunctional covers the retained full sum is made. Write
\[
 J(t)=1_{r^2\nmid t\ \text{for every }r\in I},\qquad
 \omega_I(t)=\#\{r\in I:r\mid t\},
\]
\[
 A(n)={\mu(n)J(n)\over1+\omega_I(n)},\qquad
 C(m)={b_z(m)J(m)\over1+\omega_I(m)}.
\]
On the retained set the following is exact:
\[
\begin{split}
 R_{\rm good}=-\sum_{n,m} A(n)C(m)
 \sum_{\substack{r,s\in I\\r\nmid n,\ s\nmid m}}
 &u(rn/D)w(sm/V)\sum_{p\sim P\ \mathrm{prime}}\log p\sum_{b\ge1}
 W(p/P,rsnm/Q,b/B)\\[-2mm]
 &\times\{1_{p\mid brsnm-1}-1_{p\mid brsnm+1}\}.       \tag{1}
\end{split}
\]
Indeed `mu(rn)=-mu(n)` under `r∤n`, and `b_z(sm)=b_z(m)` under `s∤m`: a prime-power divisor of `sm` either divides `m` or is `s<z`. Each original pair receives total weight
`omega_I(d) omega_I(v)/(omega_I(d) omega_I(v))=1`.
There is no assertion that `b_z(m)=log m`, and the two reciprocal counts have not been omitted.

Localize `r~R0`, `s~S0`, and write
\[
 R_0=X^\rho,\quad S_0=X^\tau,\quad 0\le\rho,\tau\le .001,
 \qquad N=D/R_0,\quad M=V/S_0,\quad \kappa=\rho+\tau.
                                                               \tag{2}
\]
Polylogarithmic lower endpoints are included in this notation. In this block the residual ranges are fixed multiples of `N,M`. If `T(n,m)` denotes the inner sum in (1), the legitimate smoothing step is
\[
 |R_{R_0,S_0}|^2\le
 \Big(\sum_{n\asymp N}|A(n)|^2\Big)
 \Big(\sum_{m\asymp M}|C(m)|^2\Big)
 \sum_{n,m}|T(n,m)|^2.                                  \tag{3}
\]
Thus both residual variables really are smooth in the **last** factor, after expanding it. The sparse arithmetic norms remain in the **first** factor. In particular this is not the invalid operation of making the original Möbius coefficient smooth. Their elementary upper bound is `O(NM L^2)`; any sharper sparse logarithmic norms may be retained without changing the power-exponent obstruction below.

It suffices for the applicability audit to examine a fixed critical annulus `b1,b2~B`, absorbing a smooth annular cutoff into `W`. This is an actual piece of the Schwartz kernel, not a replacement of its whole tail. Failing to cover this piece prevents claiming coverage of the functional. No assertion about the sum of other annuli is needed.

## 2. The four signs retain exactly the primitive product conductor

In the expansion of (3) take distinct primes `p1,p2~P`, on the fully distinct extracted-prime piece `r1!=r2`, `s1!=s2`. The same identities hold without the latter restrictions. Put
\[
 c_i=b_i r_i s_i,\qquad q=p_1p_2,\qquad
 H(t)=\sum_{\sigma_1,\sigma_2=\pm1}\sigma_1\sigma_2
 1_{c_1t\equiv\sigma_1\ (p_1)}1_{c_2t\equiv\sigma_2\ (p_2)}.
                                                               \tag{4}
\]
All `c_i` are units at `p_i`, since `c_i<<X^(.102)<p_i`. For these labels the exact smooth weight is
\[
\begin{split}
 F(n/N,m/M)={}&u(r_1n/D)\overline{u(r_2n/D)}
 w(s_1m/V)\overline{w(s_2m/V)}\\
 &\times W(p_1/P,r_1s_1nm/Q,b_1/B)
 \overline{W(p_2/P,r_2s_2nm/Q,b_2/B)}.                 \tag{5}
\end{split}
\]
It has uniform compact support and smooth seminorms. The external coefficient is exactly `(log p1)(log p2)`.

Coprimality has not disappeared: the cell also contains
`1_(n,r1r2)=1 1_(m,s1s2)=1`. Expand these as
\[
 \sum_{e\mid\operatorname{rad}(r_1r_2)}\mu(e)1_{e\mid n},
 \qquad
 \sum_{f\mid\operatorname{rad}(s_1s_2)}\mu(f)1_{f\mid m}.
\]
This gives at most sixteen cells of the following form, with `N,M` replaced by `N/e,M/f` and `c_i` by `ef c_i`. It shortens the residual intervals and does not change `q`. The formulas below apply to each term; no signed restriction is discarded.

Let `e_q(x)=exp(2 pi i x/q)` and use the **unnormalized** finite Fourier transform. CRT gives
\[
 \widehat H(h)=
 \left(e_{p_1}(-h\overline{c_1p_2})-e_{p_1}(h\overline{c_1p_2})\right)
 \left(e_{p_2}(-h\overline{c_2p_1})-e_{p_2}(h\overline{c_2p_1})\right).
                                                               \tag{6}
\]
Consequently
\[
 \boxed{\widehat H(h)=0\ \Longleftrightarrow\ (h,q)>1,
 \qquad \sum_{h\bmod q}|\widehat H(h)|^2=4q.}          \tag{7}
\]
Here the primes are odd. For a unit `h`, neither sine factor in (6) vanishes. The norm identity also follows since `H` has four distinct nonzero values, each `+1` or `-1`. Notice that `H(-t)=H(t)`: the product of the two odd residue differences is even, not odd.

Equivalently, character orthogonality gives
\[
 H(t)={4\over\varphi(q)}
 \sum_{\substack{\chi_i\bmod p_i\\\chi_i(-1)=-1\ (i=1,2)}}
 \chi_1(c_1)\chi_2(c_2)(\chi_1\chi_2)(t).             \tag{8}
\]
Every character here is primitive of conductor `q`, and globally even. Extracting `r,s` has changed the unit dilations `c_i`; it has not made the surviving conductor small or removed its Fourier mass.

## 3. Exact two-variable completion and its scale

For one of the smooth cells let
\[
 T_F=\sum_{n,m\in\mathbb Z}F(n/N,m/M)H(nm).
\]
With `hat F(xi,eta)=integral F(x,y)e(-xi x-eta y) dx dy`, two applications of Poisson give
\[
 T_F={NM\over q^2}\sum_{h,k\in\mathbb Z}
 \widehat F(Nh/q,Mk/q)\,\mathcal K(h,k),               \tag{9}
\]
\[
 \mathcal K(h,k)=\sum_{\sigma_1,\sigma_2}\sigma_1\sigma_2
 S(h,k a_{\sigma_1,\sigma_2};q),\quad
 S(a,b;q)=\sum_{x\bmod q}^{*}e_q(ax+b\bar x),          \tag{10}
\]
where `a_sigma` is the CRT class `sigma_i/c_i (mod p_i)`. This follows directly by setting `m=a_sigma/n` in the complete residue sum.

Writing `Kl_2(t;p)=p^(-1/2)S(1,t;p)` and `j=3-i`, CRT factors (10) **exactly** as
\[
 \mathcal K(h,k)=\sqrt q\,K_1(hk)K_2(hk),\qquad
 K_i(t)=\operatorname{Kl}_2(\overline{c_i}\,\overline{p_j}^{\,2}t;p_i)
       -\operatorname{Kl}_2(-\overline{c_i}\,\overline{p_j}^{\,2}t;p_i).
                                                               \tag{11}
\]
This formula includes the vanishing when `(hk,q)>1`. It is a two-variable, two-prime product trace, not a three-variable `Kl_3` sum over a prime field.

The exponent ledger for the unshortened cell is

| Quantity | Power of `X` |
|---|---:|
| `N`, `M` | `.45-rho`, `.45-tau` |
| `NM` | `.9-kappa` |
| `q=p1p2` | `1.2` |
| dual lengths `U=q/N`, `V'=q/M` | `.75+rho`, `.75+tau` |
| `U V'` | `1.5+kappa` |
| unsigned complete-density scale `NM/q` | `-.3-kappa` |

One relevant sharp **smooth** input is Blomer–Fouvry–Kowalski–Michel–Milićević, arXiv:1604.07664, Proposition `propSZ`. Its hypotheses are: `ell` is **prime**, `(a,ell)=1`, `U,V'>=1`, smooth weights supported in `[1/2,2]` with
`W_i^(j)<<_(j,epsilon)(ell^epsilon Z)^j`, `Z>=1`. For normalized `Kl_2`, it proves
\[
 \sum_{h,k}W_1(h/U)W_2(k/V')\operatorname{Kl}_2(ahk;\ell)
 \ll_\epsilon (\ell Z)^\epsilon Z^2
       \left(\sqrt\ell+{UV'\over\sqrt\ell}\right).    \tag{12}
\]
An additional smooth factor `W_3(hk/Y)` is allowed under the same derivative conditions. The target (11) is **not** (12): its modulus is composite and its trace is a product at two distinct primes. Even granting the displayed numerical bound for that product would, on insertion in (9), give only
\[
 {NM\over q^{3/2}}\left(\sqrt q+{(q/N)(q/M)\over\sqrt q}\right)
 = {NM\over q}+1,                                    \tag{13}
\]
not a saving on the sparse scale `NM/q`. The `+1` is an incomplete-product/single-hit allowance, not a principal term that the signs have been shown to cancel: the vanished zero modes are already absent in (11). This comparison is not an invocation of an unproved composite-modulus extension.

There is an elementary way to see the same pointwise scale without any extension: on the support in (5), `0<nm<<NM<q`. Each of the four classes then permits at most one positive integer product `nm`; it has `O_epsilon(X^epsilon)` divisors. Thus `|T_F|<<_epsilon X^epsilon`. Applying this **termwise** to the off-diagonal cells costs at most `(R0 S0 B P)^2 X^epsilon`. With the Cauchy prefactor `NM L^2`, this corresponds to an `R`-scale
\[
 X^{23/20+\kappa/2+\epsilon},                          \tag{14}
\]
not `o(X)`. Sharper logarithmic Ramaré norms cannot repair this fixed-power loss. The already known sparse row bound is better than (14); the calculation is an applicability obstruction, not a proposed new estimate for `R`. To improve it one must actually average the signed cells across their coupled labels, rather than bound each smooth completion separately.

## 4. Why the extracted variables do not meet the checked Type III theorem

A precise benchmark is Polymath, arXiv:1402.0811, Theorem `newtype`(v) with Definition `type-def`(iii). In its notation, `x=M0 N1 N2 N3` up to fixed factors, the coefficient at `M0` is divisor/log-bounded, and the other **three** sequences are smooth at scales `Ni` (fixed compact scaled support, each fixed derivative bounded by a power of `log x`). For fixed
\[
 0<\varpi<1/12,\quad 0<\delta<1/4+\varpi,\quad 0<\sigma<1/2,
\]
it gives arbitrary logarithmic saving for the sum of absolute progression discrepancies of that convolution, at a fixed compatible reduced residue, over squarefree `x^delta`-densely divisible moduli at most `x^(1/2+2 varpi)`, provided
\[
 N_iN_j\gtrsim x^{1/2+\sigma}\ (i\ne j),\qquad
 x^{2\sigma}\lesssim N_i\lesssim x^{1/2-\sigma},\qquad
 \sigma>{1\over18}+{28\over9}\varpi+{2\over9}\delta.   \tag{15}
\]
The source permits subpower slack in the size notation; all failures below have fixed-power gaps. A positive integer `q` is `y`-densely divisible if every `1<=R<=yq` has a divisor in `[R/y,R]`.

Use the most favorable original total length `x=BRSNM=X`. Even **pretending that the arithmetic cofactor sequences are smooth**, no grouping of the five available factors `n,m,b,r,s`, without splitting `n` or `m` further, fits (15). The two large factors must lie in distinct smooth blocks: grouping them together gives exponent at least `.898>1/2`; putting one in the unrestricted block leaves two smooth blocks whose product is at most `brs<<X^(.102)`, violating the pair-product condition. The third smooth block therefore has size at most `X^(.102)`. Hence
\[
 2\sigma\le .102,\quad\text{so}\quad
 \sigma\le {51\over1000}<{1\over18}.                  \tag{16}
\]
This already contradicts (15), even before demanding the pilot's modulus range. For `p~X^.6` that range requires `varpi>=1/20`, making the lower bound `sigma>19/90+(2/9)delta`, still worse. In reality `A(n),C(m)` are not smooth. Also every permitted `delta<1/3`: with `y=X^delta`, neither `p~X^.6` nor `p1p2` has a divisor in `[2,2y]`, so taking `R=2y` disproves dense divisibility. Extracting tiny primes from the **summation variables** does not supply divisors of these **moduli**.

This rules out this sourced Type III application; it does not rule out a further, genuinely different decomposition or a new averaged product-trace estimate. No such estimate is asserted here.

## 5. Divisor switching: an applicable determinant theorem, but the wrong error

For completeness, the closest classical signed theorem after switching does accept the exact arithmetic weights. On a critical `b~B` piece set
\[
 \gamma(q)=\sum_{dv=q}\mu(d)u(d/D)b_z(v)w(v/V).
\]
Here `q=dv` is an arithmetic summation variable, not the product modulus of §§2–3. Inserting the good-set indicators in `gamma` gives exactly the same theorem audit for (1). The equation becomes `ap-bq=-sigma`, with `a~A0=X^(2/5)`. Primality stays in the coefficient `beta(p)=1_(p prime) log p`; it is never deleted. Smooth Mellin separation of `W` reduces to the following theorem with the same support scales and unimodular twists of `gamma,beta`.

Bettin–Chandee, arXiv:1502.00769, Corollary `c1`, allows arbitrary complex sequences `alpha_(n1), beta_(n2)` at scales `N1,N2`, and smooth `f(m1),g(m2)` supported on dyadic intervals of scales `M1,M2`, with `f^(j)<<eta^j M1^(-j)`, `g^(j)<<eta^j M2^(-j)` for every fixed `j`, `eta>1`. For fixed nonzero integer `Delta`, the sum on `m1 n2-m2 n1=Delta` equals
\[
 \sum_{(n_1,n_2)\mid\Delta}
 { (n_1,n_2)\alpha_{n_1}\beta_{n_2}\over n_1n_2}
 \int f((t+\Delta)/n_2)g(t/n_1)\,dt
\]
plus an error
\[
 \ll_\epsilon (\eta\mathcal B)^{3/2}\|\alpha\|_2\|\beta\|_2
 (N_1N_2)^{7/20}(N_1+N_2)^{1/4+\epsilon}(M_1M_2)^\epsilon,
 \quad \mathcal B={M_1N_2\over M_2N_1}+{M_2N_1\over M_1N_2}. \tag{17}
\]
Here take `(m1,m2,n1,n2)=(a,b,q,p)`, `alpha=gamma`, and
\[
 (M_1,M_2,N_1,N_2)=(X^{.4},X^{.1},X^{.9},X^{.6}),\qquad
 \mathcal B\asymp1.
\]
A smooth cutoff in `a` may equal one throughout the forced range, with a fixed finite dyadic partition. The signed principal terms then cancel (alternatively their difference is bounded by `O(L^C)` by the derivative bound and `ap~X`). The error, however, is
\[
 \|\gamma\|_2\ll Q^{1/2}L^{5/2},\quad
 \|\beta\|_2\ll P^{1/2}L^{1/2},\qquad
 \boxed{\text{error}\ll_\epsilon
 X^{\,3/4+21/40+9/40+\epsilon}=X^{3/2+\epsilon}.}       \tag{18}
\]
The first norm follows simply from `|gamma(q)|<=L tau(q)` and the mean of `tau^2`; it is not a small dyadic Möbius moment. Smooth separation costs only integrable polynomial dependence on Mellin parameters. Thus this theorem really applies, but does not estimate the signed error at the required scale.

Double extraction does not justify changing `N1=Q` to `Q/(rs)` in (17): keeping `q'=nm` changes the other determinant variable to `rs b`, supported on a sublattice, not a smooth sequence of all integers. Nor can `nm` itself be treated as one smooth variable: its weight is a divisor convolution, not the scaled smooth functions required in the `m` slots. Grouping back into `q=rsnm` restores precisely the long arithmetic slot above.

## 6. Audit and stopping point

Local sources checked (no dependence on `Submission/Spec.lean`):

* `Submission/DirectOddCountResearch.md`, §13, and `Submission/CriticalBandSieveResearch.md`, especially §§1, 4–7, for the exact functional, normalization, and existing upper-bound scope.
* `/corpus/src/1604.07664/1604.07664.tex:103–132`: the prime-modulus smooth Kloosterman proposition and all its weight conditions.
* `/corpus/src/1402.0811/1402.0811.tex:462–485, 547–569, 585–639, 692–700`: dense divisibility, coefficient classes, Type III definition and parameter theorem; compare its restatement at `5783–5809`.
* `/corpus/src/1502.00769/1502.00769.tex:80–90`: the determinant corollary, not its conjectural strengthening.

`ResidualCovarianceVerification.py` checks the double Ramaré coefficients with exact rational/formal prime-log arithmetic; the four CRT classes and Fourier factors; the two-variable Kloosterman factorization as exact exponential-polynomial coefficient arrays; switching and coprimality inclusion–exclusion; and the exponent ledger, including all groupings of the five atomic factors for the Type III test. The recorded run passed 8,000 Ramaré coefficient checks, 4,194 Fourier factorizations, 2,646 double-completion factorizations, 25,600 atomic groupings, and the additional checks listed in `ResidualCovarianceVerification.log`. All are exact; no floating-point roots are used. These finite checks verify identities and bookkeeping, not an asymptotic cancellation theorem.

**Exact obstruction:** the two-variable smoothing afforded by double extraction leads to (9)–(11), at conductor `X^1.2` and residual product length `X^(.9-kappa)`. Its sign projection is fully primitive, not a conductor reduction; the checked smooth estimate is only pointwise and on the wrong sparse scale, the checked Type III theorem misses both the factor geometry and modulus hypotheses, and the applicable switched determinant estimate has error (18). There is no independently proved saving for the distinct-extracted-prime, distinct-prime-modulus covariance in this note, and hence no conclusion `R=o(X)` or ordinary-density conclusion for Erdős 371.
