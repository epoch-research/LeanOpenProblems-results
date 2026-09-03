# Signed-residue variance: an all-integer estimate in a restricted range

## Result and scope

Put `y=X^a`, `F(t)=1_{P(t)<=y}`, `P(1)=1`, and

\[
 A_q=\sum_{1\le m\le X/q}\{F(qm-1)-F(qm+1)\}.
\]

**Proposition.** For fixed `1/2<a<b<c<17/33` and every `0<eta<1`,

\[
 \boxed{\sum_{X^b<q\le X^c\atop q\in\mathbb N}
       \frac qX|A_q|^2\ll_{a,b,c,\eta}
       \frac{X}{(\log X)^{1-\eta}}.}                         \tag{1}
\]

Keeping only prime moduli gives the stronger estimate

\[
 \boxed{\sum_{X^b<q\le X^c\atop q\ {\rm prime}}
       \frac qX|A_q|^2\ll_{a,b,c,\eta}
       \frac{X}{(\log X)^{2-\eta}}.}                         \tag{2}
\]

These are deductions from the **proof ingredients** of Fouvry--Radziwill,
*Level of distribution of unbalanced convolutions*, arXiv:1811.08672,
not a new dispersion theorem. The extra point here is that **squaring the
pointwise exceptional-set bound** saves the logarithm incurred by summing
all integer moduli over a full power interval. Summing the published weak
dyadic L1 corollary alone would not prove (1).

This does **not** establish the proposed estimate for arbitrary
`a<b<c<1`, or Erdős 371. Section 3 identifies the exact unestimated term
outside the proven range. No Lean file, in particular `Spec.lean`, is
edited or used as an admitted theorem.

## 1. Endpoint normalization

Let

\[
 B_q=\sum_{t\le X,\ t\equiv-1\ (q)}F(t)
       -\sum_{t\le X,\ t\equiv1\ (q)}F(t).
\]

For `q>=3` the exact relation is

\[
 A_q=B_q+1-1_{q\mid X+1}F(X)-1_{q\mid X}F(X+1).             \tag{3}
\]

The difference has absolute value at most 1. Consequently its weighted
square sum over all `q<=X^c` is `O(X^(2c-1))`, which is smaller than either
right-hand side in (1)--(2). It suffices to estimate `B_q`.

## 2. Proof of the variance estimates

Write `L=log X` and `theta=17/33`. Choose fixed

\[
 c/\theta<\kappa<1,\qquad \rho=\sigma/2,
\]

where `sigma>0` is sufficiently small that

\[
 \sigma<a,\quad c+2\sigma<1,\quad 2\sigma<\eta,\quad
 \frac{\sigma}{\kappa}
 <\frac{17}{36}-\frac{11c}{12\kappa}-\rho.                  \tag{4}
\]

Take `T` between `X^kappa` and `2X^kappa` with `X/T` a power of two.
Set

\[
 U=\exp(L^\sigma),\qquad V=X^\sigma.
\]

Partition `(U,V]` into intervals `I_j=(v_{j-1},v_j]` of relative length
at most `L^(-4)` and comparable to this length, except possibly the last.
There are `O(L^5)` intervals. An integer is **good** if its first occupied
interval contains exactly one prime factor, counted with multiplicity.
No restriction is imposed on its later occupied intervals.

For `n>T` there is an exact decomposition

\[
 F(n)=G(n)+R(n),\qquad
 G(n)=F(n)1_{n\ {\rm good}},\quad R(n)=F(n)1_{n\ {\rm bad}},
 \qquad 0\le G,R\le1.                                    \tag{5}
\]

### 2.1 Good part: arbitrary logarithmic saving

The first-occupied-interval convention gives exactly

\[
 G(n)=\sum_j\sum_{rw=n}\beta_j(r)\alpha_j(w),
\]

where

\[
 \beta_j(r)=1_{r\ {\rm prime},\ r\in I_j},\qquad
 \alpha_j(w)=F(w)1_{\text{no prime divisor of }w\text{ lies in }(U,v_j]}.
                                                               \tag{6}
\]

Here `r<=V<y`, so `F(r)=1`. Both coefficients are 1-bounded. The prime
coefficient is Siegel--Walfisz, uniformly in the interval endpoints.
Repeated primes in the first occupied interval cannot occur in (6),
because the cofactor condition excludes them.

The analytic input is Corollary `cor:Main(i)` of the cited paper
(`FouvryRadzi7.tex`, lines 66--77). It gives an arbitrary logarithmic
saving for the L1 fixed-residue discrepancy of a divisor-bounded
convolution on `t<rw<=2t`, summed over a dyadic block of moduli of size Q,
provided its Siegel--Walfisz factor has size N satisfying

\[
 \exp((\log t)^\rho)\le N
 \le Q^{-11/12}t^{17/36-\rho}.                              \tag{7}
\]

Localize (6) dyadically. Since `t>=T>=X^kappa`, `Q<=X^c`, and
`U/2<=N<=V`, (4) verifies (7), with a fixed positive exponent margin.
The lower bound in (7) follows from `sigma>rho`. There are only
polynomially many logarithmic subdivisions. Their losses are absorbed
by the arbitrary logarithmic saving. Summing the n-intervals uses
`sum t=O(X)`, not a power-interval replacement by a single dyadic block.

The principal coprime means at residues 1 and -1 agree exactly. If
`B_q(G)` denotes their difference, with `T<n<=X`, then, for every fixed H,

\[
 \sum_{X^b<q\le X^c}|B_q(G)|\ll_H X L^{-H}.                 \tag{8}
\]

Since `0<=G<=1`, we also have `|B_q(G)|<=X/q+1`. Thus

\[
 \sum_{X^b<q\le X^c}\frac qX|B_q(G)|^2\ll_H XL^{-H}.       \tag{9}
\]

No all-residues mean square is being used here.

### 2.2 Bad part: square before summing moduli

A bad integer either has no prime factor in `(U,V]`, or is divisible by
`rs` for two primes in the same `I_j`, allowing `r=s`.
Shiu's bound, applied to the multiplicative exclusion indicator, gives,
uniformly for `q<=X^c` and `epsilon=+1,-1`,

\[
 \#\{n\le X:n\equiv\epsilon\pmod q,
               p\mid n\Rightarrow p\notin(U,V]\}
 \ll \frac X{\varphi(q)}\frac{\log U}{\log V}
 \ll_\sigma\frac X{\varphi(q)}L^{-1+\sigma}.                \tag{10}
\]

One can use Lemma `le:shiu` of the same paper, lines 307--314; its
constant is uniform for these moving 1-bounded multiplicative functions.

For the second exceptional case, `(rs,q)=1` is necessary. By (4),
`qrs<=X^(c+2sigma)<X`, so elementary progression counting gives
`O(X/(qrs))`, including its rounding error. Also

\[
 \sum_{r\in I_j\atop r\ {\rm prime}}\frac1r\ll L^{-4}.
\]

Even summing all integers in the interval proves this last bound, since
`U` exceeds every fixed power of L. Therefore

\[
 \sum_j\sum_{r,s\in I_j\atop r,s\ {\rm prime}}\frac1{rs}
 \ll L^5L^{-8}=L^{-3}.
\]

Combining the two cases gives the **pointwise-in-q** bound

\[
 |B_q(R)|\ll \frac X{\varphi(q)}L^{-1+\sigma}.               \tag{11}
\]

It follows that for any set of the permitted moduli,

\[
 \sum_{q\in\mathcal Q}\frac qX|B_q(R)|^2
 \ll X L^{-2+2\sigma}
       \sum_{q\in\mathcal Q}\frac q{\varphi(q)^2}.           \tag{12}
\]

The needed elementary harmonic estimates are

\[
 \sum_{q\le X^c}\frac q{\varphi(q)^2}\ll L,\qquad
 \sum_{X^b<p\le X^c\atop p\ {\rm prime}}
       \frac p{(p-1)^2}=\log(c/b)+o(1).                     \tag{13}
\]

For the first, expand `(q/phi(q))^2=sum_{d|q}h(d)` with squarefree support
and `h(p)=p^2/(p-1)^2-1=O(1/p)`. Interchanging the sums and using
`sum h(d)/d=product_p(1+h(p)/p)<infinity` proves it.
Equations (12)--(13) give respectively `O(XL^(-1+2sigma))` and
`O(XL^(-2+2sigma))`. This is the saving lost by summing unsquared
exceptional-set bounds over all integer moduli.

### 2.3 Small n and completion

For `F(n)1_{n<=T}`, each signed progression difference has absolute
value at most `T/q+1`. Its all-integer weighted variance is at most

\[
 \ll \frac{T^2}{X}\sum_{q\le X^c}\frac1q
          +\frac1X\sum_{q\le X^c}q
 \ll X^{2\kappa-1}L+X^{2c-1},                              \tag{14}
\]

a power saving relative to X. Combine (3), (5), (9), (12)--(14), and
`|z_1+z_2+z_3|^2<=3 sum |z_i|^2`. Since `2sigma<eta`, this proves
(1) and (2), with the full power interval retained throughout.

For any subset of the prime band, Cauchy--Schwarz and
`sum X/p=O(X)` now give signed current
`O(X/(log X)^(1-eta/2))` from (2), with at most the single original edge
endpoint. This is still only the restricted exponent range above.

## 3. Exact remaining term for general a<b<c<1

This section does not assume `c<17/33`. Put `B=X^b`, `C=X^c`, and let
`mathcal Q` be either all integers or the primes in the **full** interval
`(B,C]`. Set `M=floor(X/B)`, `K=floor((X+1)/y)`, and `H=1-F`.
For sufficiently large X, `y^2>X+1` and `2M<y`.

Write

\[
 d_m(q)=H(qm+1)-H(qm-1).
\]

The exact variance expansion is

\[
 \sum_{q\in\mathcal Q}\frac qX A_q^2=D_{\mathcal Q}+E_{\mathcal Q},
 \qquad
 D_{\mathcal Q}=\frac1X\sum_{q\in\mathcal Q}q
             \sum_{m\le X/q}d_m(q)^2\le\#\mathcal Q,        \tag{15}
\]

\[
 E_{\mathcal Q}=\frac1X\sum_{q\in\mathcal Q}q
 \sum_{m\ne n\le X/q}\sum_{\epsilon,\eta=\pm1}
       \epsilon\eta H(qm+\epsilon)H(qn+\eta).              \tag{16}
\]

Thus the entire cofactor diagonal, summed over the full band, is
`O(X^c)` (or `O(X^c/log X)` for primes). It is not the obstruction.

There is a fully explicit binary-prime version of (16). Uniqueness of
the prime factor above y gives

\[
 H(qm+\epsilon)=\sum_{kp=qm+\epsilon\atop p>y\ {\rm prime}}1.
\]

In an off-diagonal term the two large primes p,r are necessarily
**distinct**: equality would force the prime to divide the nonzero
integer `n epsilon-m eta`, whose absolute value is at most `2M<y`.

For each `m!=n`, `k,l<=K`, and signs, require

\[
 (m,k)=(n,l)=1,\qquad d=(k,l)\mid n\epsilon-m\eta.           \tag{17}
\]

Otherwise the term is zero. Put `L0=[k,l]` and let `q0 in [0,L0)` solve

\[
 q_0\equiv-\epsilon\bar m\pmod k,\qquad
 q_0\equiv-\eta\bar n\pmod l.
\]

Define the two integer affine forms

\[
 P(t)=\frac{mL_0}{k}t+\frac{mq_0+\epsilon}{k},\qquad
 R(t)=\frac{nL_0}{l}t+\frac{nq_0+\eta}{l}.                  \tag{18}
\]

Let I consist of the integers t satisfying

\[
 B<q_0+L_0t\le\min(C,X/\max(m,n)),\qquad P(t),R(t)>y.
\]

Then the **exact uncontrolled off-diagonal** for all integer moduli is

\[
 \boxed{
 E_{\mathcal Q}=\frac1X
 \sum_{m\ne n\le M}\sum_{\epsilon,\eta=\pm1}\epsilon\eta
 \sum_{k,l\le K\atop (17)}
 \sum_{t\in I}(q_0+L_0t)
             1_{P(t)\ {\rm prime}}1_{R(t)\ {\rm prime}}.
 }                                                           \tag{19}
\]

For prime moduli insert the additional condition that `q0+L0 t` is
prime. Dropping that third primality test is valid for the **original
nonnegative variance**, not termwise inside the signed sum (19).

The determinant of the two forms is

\[
 \frac{mL_0}{k}\frac{nq_0+\eta}{l}
 -\frac{nL_0}{l}\frac{mq_0+\epsilon}{k}
 =\frac{m\eta-n\epsilon}{d}.                               \tag{20}
\]

Consequently same-sign terms have determinant size `|m-n|/d`, whereas
opposite-sign terms have `(m+n)/d`. Their local factors need not agree.
For example take `m=1,n=2,k=l=1`. At the prime 3, the pair
`q+1,2q+1` has two forbidden residues, whereas `q+1,2q-1` has only one.
The normalized two-prime local factors are respectively `3/4` and
`3/2`. Simultaneously reversing both signs preserves these factors and
also preserves the variance coefficient `epsilon eta`: it does not
cancel them. For prime q, `m=2,n=4,k=l=1` gives respectively three and
two forbidden residues modulo 3 after including the q-primality test.

These examples refute **termwise** local-main-term cancellation. They
are not counterexamples to the variance bound; any fixed cofactor
family is too small to settle the full averaged problem. A proof could
still exploit cancellation after summing all the growing cofactor
variables. No such estimate is established here for general b,c.

Equation (19) requires a signed average of two simultaneous prime tests
with growing coefficients and coupled cutoffs. Ordinary one-prime
progression estimates do not evaluate it. Ordinary short-interval
smooth-number distribution does not directly supply these correlations
on the two rays `mq+epsilon`, `nq+eta` with a common q. A transfer to this
sampling constraint remains unproved here; simply dropping the constraint
by positivity does not estimate the signed difference.

The checked unbalanced-convolution input (7) cannot extend the proof
past its exponent boundary: for `Q>=t^(17/33)` its upper bound for N is
at most `t^(-rho)`, incompatible with its lower bound. The bad-set
estimate (12), by itself, remains valid for any fixed `c<1`, using only
`sigma<a` and `c+2sigma<1`, not the last condition in (4). It is the
**good convolution** that is unestimated there.

Finally, replacing the two residues by an all-residues BDH bound of
size `XQ` (up to logarithms) would give weighted bound `Q^2` (up to
logarithms), not `o(X)` when `Q>sqrt X`. Neither (1) nor (2) uses that
invalid substitution.

## Verification

`SignedResidueVarianceVerification.py` checks (3), (15)--(20) against
independent direct enumeration, for both all integer and prime moduli.
It passed 1,805 endpoint checks, 147,340 large-prime incidence checks,
and 2,158,296 compatible CRT/form checks. It also passed 72,000 exact
first-occupied-bin convolution checks, the displayed local-root tests,
12 rational parameter-margin checks, and a finite Euler-product
majorant check. These verify finite identities, not the analytic
asymptotic. The analytic input was checked directly in the cited source.

Initial and final `Spec.lean` SHA-256:
`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
