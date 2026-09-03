# Global logarithmic Vaughan smoothing: exact identity and remaining obstruction

**Status:** This is a rigorously delimited analytic test, not a proof or disproof of the ordinary-density theorem. Neither target in `Spec.lean` is used. The main assistant checked the convolution algebra, the semiprime asymptotic, the Poisson normalization in `DirectOddCountResearch.md` §13.1, and the stated GKM hypotheses in the source.

## 1. Exact globally smoothed identity

Let `1` be the constant-one arithmetic function, `ell(n)=log n`, and `epsilon` the convolution unit. Choose fixed smooth functions `0<=f,g<=1`, equal to one near zero and zero for arguments at least one. For example, integrate a nonnegative unit-mass smooth bump supported inside `(a,1)`, with fixed `0<a<1`. Set
\[
 f_d=f(\log d/\log R_\mu),\quad g_c=g(\log c/\log R_\Lambda),\quad
 \mu_f(d)=\mu(d)f_d,\quad\Lambda_g(c)=\Lambda(c)g_c.
\]
From `mu*1=epsilon` and `Lambda*1=ell`, one gets the **exact** identity
\[
 \Lambda=\Lambda_g+\mu_f*\ell-\mu_f*\Lambda_g*1
       +(\mu-\mu_f)*(\Lambda-\Lambda_g)*1. \tag{1}
\]
Thus the actual smooth Type II coefficients, before any dyadic factor subdivision, are
\[
 b_g(v)=\sum_{c\mid v}\Lambda(c)(1-g_c),\qquad
 \gamma(n)=\sum_{d\mid n}\mu(d)(1-f_d)b_g(n/d). \tag{2}
\]
One cannot retain the old sharp `b_z` while silently claiming the smooth identity (1).

Use the pilot scales
\[
 P=X^{3/5},\quad Q=X^{9/10},\quad H=X^{1/2},\quad B=X^{1/10},\quad L=\log X.
\]
The critical-band kernel remains exactly
\[
 K_0(n)=\sum_{p\sim P\ {\rm prime}}\log p\sum_{b\ge1}
 W(p/P,n/Q,b/B)(1_{p\mid bn-1}-1_{p\mid bn+1}). \tag{3}
\]
Here `W(r,t,x)=(1/(2i)) Fourier[chi(y)k(r,t,y)](-x/r)`, with the even frequency cutoff and odd real sine kernel from `DirectOddCountResearch.md` §13.1. It is real, odd and uniformly Schwartz in its last coordinate. There is **no factor H left after Poisson**. Primality of `p` is retained.

If
\[
 R_\mu R_\Lambda\le X^{3/10-\delta}
\]
for a fixed `delta>0`, both Type I free variables have length at least `Q/(R_mu R_Lambda)>=PX^delta`. In the sine representation their periodic functions have complete mean zero, including zero values on nonunits. Smooth completion therefore makes both Type I sums smaller than any fixed power of `X`; a sufficient explicit bound before choosing the number of integrations is
\[
 |T_I|\ll_J PQL^2(P R_\mu R_\Lambda/Q)^J. \tag{4}
\]
The constants depend on the fixed smooth cutoffs and their seminorms, not on `X`. Setting both support cutoffs equal to `X^.14` leaves a `.02` power margin. If both tails must still be supported strictly above `z=X^.14`, take `R_mu=R_Lambda=X^.145` and fixed `f,g` equal to one up to `28/29`, smoothly transitioning to zero at one. This leaves a `.01` margin.

Since `Lambda_g(n)=0` on the `Q`-support, the critical prime-`q` sum equals `sum_n gamma(n)K_0(n)` up to Type I errors and proper prime powers. The latter cost at most `O(X^.55 L^2)`: there are `O(Q^.5)` of them, their von Mangoldt weights are at most `L`, and `K_0^+<<BL`. This does not change the prime condition on `p`.

## 2. Opening the smooth remainder

Define the genuine fixed-profile GKM divisor sum
\[
 M_f(m;R_\mu)=\sum_{d\mid m}\mu(d)f_d.
\]
Writing `Lambda_t=Lambda-Lambda_g`, the convolution in (2) gives
\[
 \gamma=\Lambda_t-\Lambda_t*M_f,
\]
and, since `M_f(1)=1`,
\[
 \boxed{\gamma(n)=-\sum_{c\mid n,\ c<n}\Lambda(c)(1-g_c)M_f(n/c;R_\mu).} \tag{5}
\]
In particular `gamma(q)=0` for every prime `q`.

For two distinct primes `r,s`, however, the exact value is
\[
 \gamma(rs)=-(1-f_r)(1-g_s)\log s-(1-f_s)(1-g_r)\log r. \tag{6}
\]
Thus
\[
 \boxed{r,s>\max(R_\mu,R_\Lambda)\quad\Longrightarrow\quad
 \gamma(rs)=-\log(rs).} \tag{7}
\]
More generally, an integer with all prime factors above both supports has `gamma(n)=Lambda(n)-log n`. Logarithmic smoothing cannot change this component. Each support cutoff is below `X^{.3+o(1)}` if their product obeys the Type I constraint and both exceed one. Hence primes with exponents close to `.45` are necessarily untouched.

## 3. The global unweighted remainder is not o(Q)

Let `0<=psi in C_c^infinity((1,2))` be fixed and nonzero. Fix exponents `a<b<.45` above both cutoff exponents. The semiprimes with
`X^a<r<=X^b`, `s` prime, and `rs/Q` in the support of `psi` have `r<s` for large `X`, so there is no double counting. PNT and partial summation give
\[
 \sum_{\substack{r,s\ {m prime}\\X^a<r\le X^b}}
 \psi(rs/Q)|\gamma(rs)|
 \sim Q\left(\int\psi\right)
 \log\frac{b(.9-a)}{a(.9-b)}. \tag{8}
\]
For detail, uniformly for `r` in this range,
\[
 \sum_s\psi(rs/Q)\log(rs)
 =(1+o(1))\frac{Q}{r}\frac{.9L}{\log(Q/r)}\int\psi.
\]
Prime partial summation in `r` converts the multiplier into
`.9 integral_a^b dt/[t(.9-t)]`, whose integral is exactly the logarithm in (8). All prime ranges stay above a fixed positive power of `X`, so the ordinary PNT errors are uniform here. For `a=.4,b=.44`, the constant is `log(55/46) integral psi>0`.

Consequently **no admissible global smoothing of this kind gives `sum_{n~Q}|gamma(n)|=o(Q)`**. This is a theorem about the unweighted coefficient norm, not about the prime-weighted signed count. A fixed narrow dyadic factor block contributes only order `Q/L`; a fixed power-width range contains order `L` such blocks. There is no contradiction with the previously proved per-block small-factor-count upper bounds.

## 4. What GKM actually supplies

Source personally checked: Granville--Koukoulopoulos--Maynard, `/corpus/src/1606.06781/1606.06781.tex`.

* Lines 351--370, `thm-smooth`: fix `k>=1`, `epsilon in (0,1)`, and a **fixed** function supported in `(-infinity,1]`, with bounded derivatives through an integer order `A>=2`. If `A>binom(2k,k)/(2k)`, then for `T>=R>=2` and `log2/logR<=eta<=1`,
  \[
  \sum_{m\le T,\ \exists p\mid m:\ p\le R^\eta}M_f(m;R)^{2k}
  \ll_{f,k,\epsilon}\eta T/\log R.
  \]
  If `f(0)!=0`, the positive-constant moment asymptotic is
  \[
  T^{-1}\sum_{m<T}M_f(m;R)^{2k}
  =c_{k,f}/\log R+O_{f,k,\epsilon}((\log R)^{-2+\epsilon}),
  \]
  requiring `T>=R^{2k}log^2 R`.
* Lines 489--503, `thm-smooth-factors`: under the same high-smoothness hypothesis,
  \[
  \sum_{m<T,\ \Omega(m;R)\ge C}M_f(m;R)^{2k}
  \ll_{k,f}T/(C\log R),\qquad T\ge R\ge2,\ C\ge1.
  \]
  `Omega(m;R)` counts prime factors at most `R`, with multiplicity.

In particular the **concentration upper bounds do not require the longer range needed for the full moment asymptotic**. Neither statement concentrates only on primes. Primes `m>R` have `M_f(m;R)=1`, lie in neither exceptional set, and generate the invariant semiprime contribution in (8).

For (5) with `R_mu=X^.14`, the second-moment asymptotic at length `T~Q/c` requires `c<<Q/(R_mu^2 log^2 R_mu)`. This is valid when `c~X^.45`, but not for every divisor `c`. Even where valid, it does not remove (8). The constants are not uniform in an arbitrarily changing profile or a growing moment order.

## 5. Complementation repairs a length inequality, not the argument

For the original dyadic coefficient with `d~D`, `v~V`, open `b_z` and put `m=n/c`. The exact complementary-divisor identity is
\[
 \gamma_{D,V}(n)=\sum_{c\mid n,c>z}\Lambda(c)
 \sum_{e\mid m}\mu(m/e)u(m/(eD))w(ce/V). \tag{9}
\]
Only if `m` is squarefree may one rewrite `mu(m/e)=mu(m)mu(e)`. Squarefreeness of the original `d` does **not** imply squarefreeness of `m`.

The complementary scale is `E=V/c`, with averaging length `M=Q/c`. At `D=V=X^.45`,
\[
 M/E^2=c.
\]
Thus `c>z` gives a power margin for a second long moment when `E` grows. For a `2k`-th moment and `c=X^kappa`, a fixed-power margin would instead require
\[
 \kappa>.9(k-1)/(2k-1);
\]
for the fourth moment this means `kappa>.30`.

This is not yet a valid fixed-profile GKM application. With `R_c` comparable to `max(2,V/c)`, the actual profile is
\[
 F_{m,c,X}(t)=u(m/(D R_c^t))w(cR_c^t/V).
\]
It depends on the averaged variable `m`, and dyadic factor cutoffs have width `O(1/log R_c)` in `t`. Their derivatives therefore cost powers of `log R_c`. Smoothing only the original `d` cutoff does not remove the dyadic `v` cutoff. Removing all factor cutoffs returns to the global identity (5), with its semiprime mass, not to a uniformly fixed profile at scale `V/c`.

Moreover, on the prime-`v` sector one has `c=v~V`, `e=1` and `E~1`. There is then no growing logarithm to save. If `m` is also prime, its remaining Möbius sign is the constant `-1`, not a source of cancellation.

## 6. Exact unresolved norm and scope

Let `K_0^+` be the positive envelope of (3). The full-tail prime-divisor argument gives `K_0^+(n)<<BL`. A compatible sufficient estimate would be
\[
 \sum_{n\sim Q,\ n\ {m composite}}|\gamma(n)|K_0^+(n)=o(BQ)=o(X). \tag{10}
\]
The GKM integer moments do not prove this prime-weighted estimate. Equation (10) includes the nonnegative contribution `sum_{n in S}log n K_0^+(n)` from the explicit semiprime family in (8). A new bound for that prime-divisibility functional, or signed cancellation in the actual `K_0`, remains necessary.

**No lower bound for the weighted expression (10) is asserted.** The proved obstruction is to global unweighted coefficient deletion and the stated smoothing/complementation inferences. It does not exclude every global cancellation argument, does not prove that a dyadic block must be handled separately, and does not settle even this entire critical band, much less the ordinary LPF density theorem.
