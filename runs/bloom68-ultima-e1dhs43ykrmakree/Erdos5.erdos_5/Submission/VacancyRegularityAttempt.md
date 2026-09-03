# Vacancy regularity: exact boundary flux and the first missing estimate

**Outcome.** Q3 is not proved. The actual vacancy mask gives an exact
right/left boundary-flux identity. Its positive strip-collision terms **can**
be bounded at the Q3 scale, including the required `L1` test norm, using the
ordinary **three-prime upper sieve**. The common signed endpoint flux remains
uncontrolled. Below it is displayed explicitly; neither summation by parts
nor removing the mask eliminates it. No Lean file or admitted lemma was added.

## 0. Independently checked baseline and conditional unique-continuation closure

This section records the main agent's independent check. It supplies no new
prime-correlation estimate.

Let `I_X` index the consecutive primes whose two endpoints lie in `[X,2X]`,
let `d_n` be their gaps, and put

```
V_X(t) = X^(-1) sum_(n in I_X) (d_n-t log X)_+,
mu_X = (log X/X) sum_(n in I_X) delta_(d_n/log X).
```

Exactly, in distributions on `(0,infinity)`, `V_X''=mu_X`.
Telescoping gives `0<=V_X(t)<=V_X(0)<=1` for `t>=0`. PNT places the first
and last primes of the window at `X+o(X)` and `2X-o(X)`, respectively,
so `V_X(0)->1`; it also gives `mu_X([0,infinity))->1`.
Thus the curves have a uniform Lipschitz bound and a locally uniformly
convergent subsequence, including at `t=0`.

For distinct prime endpoints in this window, the ordinary upper sieve gives
`T_X(h)<=C X/(log X)^2 * S(0,h)`, uniformly for `h=O(log X)`.
Inadmissible tuples contribute zero: a prime at most the tuple cardinality
would divide one endpoint, which is larger than that prime. For admissible
tuples the positive upper-sieve estimate is sufficient. In particular,
prime-power exceptional terms in a displayed von Mangoldt formulation are
not being asserted to vanish for inadmissible tuples.

The same local-factor check as below gives `S(0,h)<=F(h)`, with
`F(h)=prod_(p|h)(1-1/p)^(-2)`. Its finite Cesaro mean therefore implies,
for each fixed `0<=a<b`,

```
mu_X((a,b)) <= K(b-a)+o(1)
```

for an absolute, unoptimized `K`. The limit measure has no atom at zero
and has density bounded by `K`. Consequently a limiting curve is locally
`C^(1,1)`. More importantly, the exact positive-part identity gives

```
V_X(t)=V_X(0)-t*mu_X([0,infinity))
       + integral_(0,t) (t-s) dmu_X(s),
V(t) <= 1-t+K*t^2.
```

For a sufficiently small positive `t`, this is less than `V(0)=1`.
Thus every such limiting curve is nonconstant. No uniform integrability
of the first gap moment is needed; a possible escaped first moment only
changes the limiting constant at infinity.

Here is the conditional closure motivating Q3. If one such limit belongs
locally to the Denjoy--Carleman class

```
|V^(r)| <= A_I B_I^r M_r,
M_0=1, M_r=r! * product_(m=1..r) log(m+e),
```

with constants independent of `r` on each compact `I` in `(0,infinity)`,
then it is quasi-analytic: `M_r/M_(r-1)=r log(r+e)` is increasing and
`sum M_(r-1)/M_r` diverges. An eventual missing normalized-gap band, with
strict interior margins, makes `V_X` and hence `V` affine on a nonempty
open interval. Subtracting that affine function and using quasi-analytic
uniqueness propagates equality throughout the connected positive axis.
A globally affine bounded function there is constant, contradicting the
preceding inequality. PNT transfers `log X` to the logarithm of the global
prime index, exactly as required in the original specification.

**The derivative bounds in this paragraph are unproved hypotheses, not
available theorems about the prime gaps.** Q3 is only the first new
regularity step and does not alone supply quasi-analyticity.

## 1. Exact finite identities, with endpoint cutoffs included

Put `P_n = 1_{n prime, X <= n <= 2X}` and extend it by zero on all other
integers. This avoids boundary-error bookkeeping: when both endpoints lie in
the window, its interior mask is exactly the original prime mask. Write

\[
 M_h(n)=\prod_{1\le a<h}(1-P_{n+a}),\quad
 A_h(n)=P_nM_h(n),\quad T(h)=\sum_n A_h(n)P_{n+h}\qquad(h\ge1).
\]

For integers `ell >= 1`, nested windows and the **first** occupied site of the
new strip give

\[
 M_{h+\ell}(n)=M_h(n)\prod_{a=h}^{h+\ell-1}(1-P_{n+a}),\qquad
 1-\prod_{a=h}^{h+\ell-1}(1-P_{n+a})
 =\sum_{r=0}^{\ell-1}P_{n+h+r}\prod_{a=h}^{h+r-1}(1-P_{n+a}).
\]

Consequently the following is exact, not a sieve approximation:

\[
 \boxed{T(h+\ell)-T(h)=D^R(h,\ell)-B^R(h,\ell)} \tag{1}
\]
\[
 D^R(h,\ell)=\sum_n P_nM_h(n)(P_{n+h+\ell}-P_{n+h}),
\]
\[
 B^R(h,\ell)=\sum_{s=1}^{\ell}\sum_n
 P_nP_{n+h+\ell-s}P_{n+h+\ell}M_{h+\ell-s}(n)\ge0. \tag{2}
\]

Here the first two primes in each summand of (2) are consecutive; the last
two need not be. Expanding the **last** occupied site of a new left strip
similarly gives

\[
 T(h+\ell)-T(h)=D^L(h,\ell)-B^L(h,\ell), \tag{3}
\]
\[
 D^L(h,\ell)=\sum_n(P_{n-\ell}-P_n)M_h(n)P_{n+h},
\]
\[
 B^L(h,\ell)=\sum_{s=1}^{\ell}\sum_n
 P_nP_{n+s}P_{n+h+\ell}M_{h+\ell-s}(n+s)\ge0.
\]

Now it is the last two primes that are consecutive. In particular,

\[
 \boxed{D^R-D^L=B^R-B^L.} \tag{4}
\]

This is useful signed cancellation between the two boundary fluxes, but
**both outward fluxes have the same sign in (1)/(3)**. They do not cancel the
derivative of `T`.

## 2. The collision terms really have the Q3 scale

Fix `I=[alpha,beta]` in `(0,infinity)`, `phi` smooth with compact support in
its interior, `0 < epsilon < alpha/2`, `L=log X`, and
`ell=floor(epsilon L)`. Limits here take `X -> infinity` **first**, with
`epsilon` fixed. Let

\[
 U_X(a,b)=\sum_nP_nP_{n+a}P_{n+b}\quad(0<a<b).
\]

The ordinary fixed-order upper sieve, for shifts `O_I(L)`, gives

\[
 U_X(a,b)\ll_I \frac X{L^3}\mathfrak S(0,a,b). \tag{5}
\]

Only the positive errors are unmasked:

\[
 B^R(h,\ell)\le\sum_{s\le\ell}U_X(h+\ell-s,h+\ell),\quad
 B^L(h,\ell)\le\sum_{s\le\ell}U_X(s,h+\ell). \tag{6}
\]

Here is an elementary way to obtain the needed *localized* singular-series
average, without assuming any tuple asymptotic. Set

\[
 F(m)=\prod_{p\mid m}(1-1/p)^{-2}.
\]

Local factors show

\[
 \mathfrak S(0,k,k+s)\le F(k)F(s)F(k+s). \tag{7}
\]

Indeed a prime not dividing `ks(k+s)` has local factor at most 1; a prime
dividing it has factor at most `(1-1/p)^(-2)`. Inadmissible tuples have zero
singular series. For each fixed `q>0`,

\[
 \frac1H\sum_{m\le H}F(m)^q\longrightarrow
 c_q=\prod_p\left(1+\frac{(1-1/p)^{-2q}-1}{p}\right)<\infty. \tag{8}
\]

Proof: expand `F(m)^q=sum_{d|m} a_q(d)`, where `a_q` is nonnegative,
squarefree-supported and `a_q(p)=O_q(1/p)`; dominated convergence uses
`sum_d a_q(d)/d < infinity`. Partial summation also gives, for fixed
nonnegative continuous `w` supported in `I`, uniformly for integer
`0 <= u <= epsilon L`,

\[
 \sum_h w(h/L)F(h+u)^2=(c_2+o_{w,\epsilon}(1))L\|w\|_1.
\]

Use (7) and weighted Cauchy--Schwarz for the two factors
`F(h+ell-s)` and `F(h+ell)`, then sum `F(s)` by (8). Reflection of offsets
makes the same calculation work for the left error. Thus (5)--(8) prove

\[
 \sum_h |\phi(h/L)|B^\sigma(h,\ell)
 \ll_I \frac{\ell X}{L^2}\|\phi\|_1
       +o_{\phi,\epsilon}\!\left(\frac{\ell X}{L^2}\right),
 \qquad \sigma\in\{R,L\}. \tag{9}
\]

The implied constant is independent of small fixed `epsilon`. In particular,
(4) yields the genuine signed estimate

\[
 \limsup_{j\to\infty}\frac{L_j^2}{\ell_jX_j}
 \left|\sum_h\phi(h/L_j)(D^R-D^L)(h,\ell_j)\right|
 \ll_I\|\phi\|_1. \tag{10}
\]

A two-prime bound alone can count the new-strip collisions after forgetting
the predecessor, but that only gives `||phi||_infinity`; (7)--(9) supply the
important localization in the predecessor-gap variable. At no point was a
signed masked expression replaced by its unmasked analogue.

## 3. Exact reduction of Q3 and the unsupported term

Here `mu_X=(L/X) sum_h T(h) delta_(h/L)`, so the Q3 functional is
`int phi' dmu_X = (L/X) sum_h T(h) phi'(h/L)`.
Extend `T(h)=0` for `h<=0`, put `epsilon_X=ell/L`, and define
`D^-_epsilon phi(t)=(phi(t)-phi(t-epsilon))/epsilon`. Summation by parts gives

\[
 \int D^-_{\epsilon_X}\phi\,d\mu_X
 =-\frac{L^2}{\ell X}\sum_h\phi(h/L)[T(h+\ell)-T(h)]. \tag{11}
\]

The difference between the left side and `int phi' dmu_X` is at most
`(epsilon_X/2) mu_X([0,infinity)) ||phi''||_infinity`. PNT makes this mass
`1+o(1)`. Combining (1), (9), and (11), the **first missing estimate** is

\[
 \boxed{\limsup_{\epsilon\downarrow0}\limsup_{j\to\infty}
 \left|\frac{L_j^2}{\ell_jX_j}
 \sum_{h,n}\phi(h/L_j)P_nM_h(n)
       (P_{n+h+\ell_j}-P_{n+h})\right|
 \le C_I\|\phi\|_1,
 \quad \ell_j=\lfloor\epsilon L_j\rfloor.} \tag{F}
\]

All indicators in (F) refer to the `j`-th window. This would give Q3; the
controlled collision term and the `epsilon ||phi''||_infinity` error are
already accounted for. Finite-`X` uniform derivative bounds are **not**
asserted: `mu_X` is atomic, and the order of limits matters.

Taking absolute values before summation in (F), the ordinary pair upper
sieve and its singular-series mean yield only

\[
 \frac{L^2}{\ell X}\left|\sum_h\phi(h/L)D^R(h,\ell)\right|
 \ll_I\epsilon^{-1}\|\phi\|_1+o_{\phi,\epsilon}(1). \tag{12}
\]

The missing saving is exactly the factor `ell/L`, not an endpoint error.
Equivalently, direct termwise bounds on Q3 give `||phi'||_1`.

### Why the remaining telescoping attempts do not close (F)

* **Shift the base point.** The exact identity is
  \[
  D^R(h,\ell)=\sum_nP_{n+h}[A_h(n-\ell)-A_h(n)]. \tag{13}
  \]
  The unweighted sum of the bracket vanishes, but the remaining prime
  factor prevents that telescope. Moving the hole window between its two
  positions gives (4)/(10), not a bound for their common flux.
* **Remove the mask first.** With `R_X(h)=sum_n P_n P_{n+h}`, the exact
  first-interior-prime expansion is
  \[
  D^R(h,\ell)=R_X(h+\ell)-R_X(h)-E_X(h,\ell), \tag{14}
  \]
  \[
  E_X(h,\ell)=\sum_{1\le k<h}\sum_n
  P_nP_{n+k}M_k(n)(P_{n+h+\ell}-P_{n+h}).
  \]
  This is another **signed masked** flux, over the full interior width
  `h`, not the thin width `ell`. Its positive majorant has no small
  `ell/L` factor. Even a hypothetical unmasked signed bound could not be
  transferred through the mask without a new estimate for this term.
* **Use survival tails.** Exactly `T(h)=S(h)-S(h+1)` for
  `S(h)=sum_n P_n M_h(n)`. This merely moves another difference onto the
  test function; it supplies no improvement from `||phi'||_1` to `||phi||_1`.

## 4. Source scope and regularity sanity check

`/corpus/src/0809.2967/0809.2967.tex:921-951` (Bazzanella--Languasco--Zaccagnini,
*Prime numbers in logarithmic intervals*) states Klimov's **unmasked**
fixed-order upper sieve for distinct shifts:

\[
 \sum_{m\le Y}\prod_{i=1}^r\Lambda(m+h_i)
 \le(2^r r!+\eta)Y\mathfrak S(h_1,\ldots,h_r).
\]

The `r=2` case is the ordinary pair upper input; `r=3` supplies (5), by
positive domination with `Y=2X` and division by `L^3` on prime endpoints
in `[X,2X]`. Only logarithmic-size shifts and fixed `r` are needed. The
passage says nothing about consecutiveness, a vacancy-conditioned prime
increment, signed cancellation, or a pair/tuple asymptotic. In fact the
asymptotic is introduced separately as a **conjectural assumption** at
lines 958--978. No such assumption is used above.

The finite identities and nonnegative moment bounds cannot by themselves
force Q3. For example, a stationary renewal process with mean-one gap density
`f=1_(1/2,3/2)` has `V''=f`, bounded local tuple densities (ordered intensities
are products of `u=sum_{k>=1} f^{*k}`, locally a finite sum), but
`V'''=delta_(1/2)-delta_(3/2)`. Tests of height one and shrinking support at
`1/2` violate Q3. This is a structural sanity check, **not** a prime or an
arithmetic-sieve counterexample. Smoothing this gap density to a symmetric
compactly supported bump gives a `C^infinity` vacancy curve, affine on an
open interval, which is still not quasianalytic. Thus even proving Q3 would
only give a locally Lipschitz limiting gap density; the required all-orders
Carleman growth remains a separate, unproved target.

## 5. Verification and protected file

`check_vacancy_regularity_identities.py` exhaustively tests finite binary
words, with zero extension at the endpoints. It checks (1)--(4), (6),
(11) as integer summation by parts, (13)--(14), the first/last-occupation
expansions, survival tails, and
`W(h-1)-2W(h)+W(h+1)=T(h)` for `W(k)=sum_gaps (d-k)_+`.
Run: `python3 Submission/check_vacancy_regularity_identities.py --max-length 10`.
Result: **PASS**, 2,047 binary words of lengths 0--10 and 102,333
`(word,h,ell)` cases, including shifts exceeding the window. Python compilation
also passed. This is finite algebra verification, not evidence for an
asymptotic estimate.

`Submission/Spec.lean` was not edited. Its recorded SHA-256 is
`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.
