# Finite-q reflection: a quantitative almost-permutation theorem

## Scope

This note gives an unconditional estimate for the **complete finite-q fibers** of the largest-prime-factor reflection. It does not prove Erdős 371 or replace ordinary natural density by another density. `Submission/Spec.lean` is not edited or used as a theorem. The analytic input in the estimate is the classical Weil bound for complete Kloosterman sums, combined below with an elementary Selberg upper sieve.

Write `P(1)=1`, let `s(n)=sgn(P(n+1)-P(n))`, and, for `n>=2`, put

\[
p(n)=\min(P(n),P(n+1)),\quad q(n)=\max(P(n),P(n+1)),\quad
T(n)=p(n)q(n)-n-1.
\]

Only points with `T(n)>0` are considered in the dynamics. For a prime q, denote their full finite fiber by

\[
V_q=\{n\ge2:q(n)=q, T(n)>0\}.
\]

## 1. Exact cofactor coordinates

Write the q-divisible member of the consecutive pair as `kq`, and the other member as

\[
a=kq-s(n)=pb.
\]

Then `T(n)>0` is equivalent to `k<p`. In this case `1<=b<q`, and the reflected pair has q-side cofactor `p-k` and other member

\[
a'=p(q-b).
\]

Consequently

\[
s(Tn)=-s(n),\qquad q(Tn)=q,\qquad
p(Tn)=\max(p,P(q-b))\ge p.                                      \tag{1}
\]

The reflected point is again in `V_q`. If `p'=p(Tn)`, then

\[
T^2n=n+q(p'-p).                                                   \tag{2}
\]

Thus both parity subsequences are nondecreasing. Every nonterminal step strictly increases the smaller prime; equality is equivalent to being on a 2-cycle. There are no longer cycles.

There is a particularly short enumeration of the **entire** fiber. For each prime `p<q`, let

\[
u=u_q(p)\in\{1,\ldots,q-1\},\qquad pu\equiv1\pmod q.
\]

The only possible points with labels `(p,q)` are

\[
v^-_{p,q}=pu-1,\qquad v^+_{p,q}=p(q-u).                           \tag{3}
\]

The first is present exactly when `P(u)<=p`, and has sign -1. The second is present exactly when `P(q-u)<=p`, and has sign +1. If both are present, they are a 2-cycle. If exactly one is present, it is transient. In particular there are at most two states per prime pair, not q or pq states.

For completeness, the incoming multiplicity also has an exact factorization formula. At a state with q-side `kq`, other member `a=kq-s(n)`, and smaller prime `p=P(a)`,

\[
\deg_q^-(n)
=\sum_{r\mid a\atop r\ {\rm prime},\ k<r\le p}
  1_{P(q-a/r)\le r}.                                             \tag{4}
\]

The corresponding preimage is `rq-n-1`. Thus incoming multiplicity is not a free graph parameter: it is an explicitly restricted prime-divisor sum.

## 2. New estimate: only O(q/log^2 q) non-cycle states

Define the number of bad cofactor incidences

\[
B(q)=\sum_{p<q\atop p\ {\rm prime}}
\left(1_{P(u_q(p))>p}+1_{P(q-u_q(p))>p}\right).
\]

**Theorem.** Uniformly over primes q,

\[
\boxed{B(q)\ll \frac{q}{(\log q)^2}.}                             \tag{5}
\]

It follows that

\[
|V_q|=2\pi(q-1)-B(q),\qquad
\#\{\text{transient states in }V_q\}\le B(q).                     \tag{6}
\]

So a proportion `1-O(1/log q)` of the full fiber is already on terminal 2-cycles. This is a quantitative arithmetic assertion, not just the general fact that finite orbits eventually cycle.

### 2.1 A prime modular-inverse upper sieve

Let `I,J` be intervals in `[1,q-1]` of lengths H,L, and let `c` be nonzero modulo q. Then

\[
\#\{x\in I,y\in J:x,y\text{ prime}>q^{1/32},\ xy\equiv c\pmod q\}
\ll \frac{HL}{q\log^2q}+q^{5/8}\log^2q.                          \tag{7}
\]

Here and below a change of the absolute constant handles the finitely many small q.

Here is a derivation, including the sieve level. Fourier completion and Weil's Kloosterman bound give, uniformly for positive integers `d,e<q`,

\[
\#\{x\in I,y\in J:d\mid x,e\mid y,xy\equiv c\pmod q\}
=\frac{HL}{qde}+O(q^{1/2}\log^2q).                              \tag{8}
\]

After dividing by d and e, the variables still range in intervals modulo q. Endpoint rounding contributes only `O(1)`, absorbed in (8).

Put `z=floor(q^(1/32))` and

\[
G(z)=\sum_{d\le z}\frac{\mu^2(d)}{\varphi(d)}\gg\log z.
\]

The one-dimensional Selberg coefficients

\[
\lambda_d=\frac{\mu(d)d}{\varphi(d)G(z)}
\sum_{h\le z/d\atop(h,d)=1}\frac{\mu^2(h)}{\varphi(h)}
\quad(d\le z)
\]

satisfy

\[
\lambda_1=1,\quad
\sum_{d,e\le z}\frac{\lambda_d\lambda_e}{[d,e]}=G(z)^{-1},\quad
\sum_{d\le z}|\lambda_d|\ll z.                                  \tag{9}
\]

For the quadratic identity, use `1/[d,e]=(d,e)/(de)` and diagonalize with `sum_{r|d,e} phi(r)`. Equivalently the minimizing diagonal variables are `mu(r)/(phi(r)G(z))`. Also `|lambda_d|<=d/phi(d)`, whose sum is `O(z)`.

For primes exceeding z, each of the nonnegative sieve weights

\[
\left(\sum_{d\mid x,d\le z}\lambda_d\right)^2,
\qquad
\left(\sum_{e\mid y,e\le z}\lambda_e\right)^2
\]

is exactly 1. Multiply them and apply (8) with the two least common multiples, both at most `z^2<q`. The main term is `HL/(qG(z)^2)`. The total remainder is at most

\[
O\left(q^{1/2}\log^2q\left(\sum_{d\le z}|\lambda_d|\right)^4\right)
=O(q^{5/8}\log^2q),
\]

proving (7). No assertion about the distribution of prime inverses in intervals shorter than this error is used.

### 2.2 Applying the sieve to complements

Primes `p<=q^(3/4)` contribute at most `2*pi(q^(3/4))=O(q^(3/4))` to B(q).

For a bad incidence with larger p, write its nonsmooth cofactor as `ar`, where `r=P(ar)>p`. Then

\[
par\equiv\pm1\pmod q,\qquad ar<q.                              \tag{10}
\]

If `H/2<p<=H`, then `a<2q/H`. For each fixed a, apply (7) to p in this dyadic interval and prime `r<=q/a`; both actual primes exceed `q^(3/4)`. Dropping `r>p` only increases the upper bound. The contribution of this dyadic interval, for either sign, is

\[
\ll \sum_{a\le2q/H}
\left(\frac{H}{a\log^2q}+q^{5/8}\log^2q\right)
\ll \frac{H\log(2q/H)}{\log^2q}
 +\frac{q^{13/8}}H\log^2q.                                     \tag{11}
\]

Sum over `H=q/2^j` down to `H` comparable to `q^(3/4)`. The first terms sum to `O(q/log^2q)`, because `sum (j+1)/2^j` converges. The remainders sum to `O(q^(7/8)log^2q)`, which is also `O(q/log^2q)` asymptotically. This proves (5).

## 3. Genuine weighted balance, uniform through iteration

Let `mu_q` be counting measure on `V_q`, and `nu_q` counting measure on its 2-cycle states. The latter is exactly T-invariant. Therefore, for every integer `j>=0`,

\[
\boxed{\|T_*^j\mu_q-\mu_q\|_1
 \le2\#\{\text{transients in }V_q\}
 \ll q/\log^2q.}                                                \tag{12}
\]

The bound is uniform in the number of iterations, including after all transients have reached cycles.

More generally, for any weights `w(q,p)` constant on the two orientations of a prime pair,

\[
\left|\sum_{n\in V_q}s(n)w(q,p(n))\right|
\ll \sup_{p<q}|w(q,p)|\frac q{\log^2q}.                         \tag{13}
\]

There is also an explicit **exact** positive weighted balance, using (4):

\[
w_q(n)=\tfrac12(1+\deg_q^-(n)),\qquad
\sum_{n\in V_q}s(n)w_q(n)=0,\qquad
\sum_{n\in V_q}|w_q(n)-1|\ll q/\log^2q.                        \tag{14}
\]

Indeed `sum s(n)deg^-(n)=sum s(Tn)=-sum s(n)`, and the last inequality is half of (12) for `j=1`. These degree weights are an edge-endpoint balance; they are not asserted to be invariant under the deterministic T map.

As a corollary, if one counts **whole** fibers with `q<=Q`, then

\[
\sum_{q\le Q}|V_q|
=\pi(Q)(\pi(Q)-1)+O(Q^2/\log^3Q),\qquad
\left|\sum_{q\le Q}\sum_{n\in V_q}s(n)\right|
\ll Q^2/\log^3Q.                                                \tag{15}
\]

The ascent proportion in this ordering is `1/2+O(1/log Q)`. This is not the natural ordering `n<=X`.

No formula here asserts invariance of `1/n`, `dn/n`, or logarithmic density under T.

## 4. Natural prefixes: a uniform all-odd-iterate escape estimate

From (2), for every odd `j>=1`,

\[
T^j(n)\ge T(n).                                                 \tag{16}
\]

Consequently, even allowing the odd iteration count to depend arbitrarily on n,

\[
\#\{n\le X:Tn>0,\ T^{j(n)}n\le Y\}
\le2\#\{p<q\text{ primes}:pq\le X+Y+1\}
\ll \frac{(X+Y)\log\log(X+Y)}{\log(X+Y)}.                       \tag{17}
\]

The first implication is `pq=n+Tn+1<=X+Y+1`, and (3) gives at most two sources for each prime pair. In particular the bound is `o(X)` for `Y=CX`, with any fixed C, uniformly through all odd iterations. It also remains `o(X)` for `Y=X L(X)` if `L=o(log X/log log X)` and `L>=1`.

This yields a **linear lower bound**, not an upper bound, for the natural-prefix pushforward defect. Define

\[
A_X=\{2\le n\le X:Tn>0\},\qquad \mu_X=\sum_{n\in A_X}\delta_n.
\]

The one-variable smooth-number estimate at exponent 1/2 gives

\[
|A_X|\ge (2\log2-1+o(1))X.                                     \tag{18}
\]

Indeed the intersection of `P(n)>sqrt(X+1)` and `P(n+1)>sqrt(X+1)` has at least this many points, by a union bound, and all are active. The one-variable proportion above this threshold is `log 2+o(1)`, obtained directly by summing `floor((X+1)/r)` over primes `r>sqrt(X+1)`.

For any map `F_X(n)=T^{j(n)}n` with all `j(n)` odd and positive, (17) therefore gives

\[
\boxed{\tfrac12\|(F_X)_*\mu_X-\mu_X\|_1
\ge (2\log2-1-o(1))X.}                                         \tag{19}
\]

For example, test the two measures on `[1,2X]`: almost all transported mass has left it, while all the original mass is there. Weights that differ from unit source weights by only `o(X)` in l1 cannot remove this obstruction. This does **not** rule out a genuinely nonlocal, signed or renormalized transport argument.

## 5. The precise natural-density gap

The signed count of active points in a natural prefix is exactly

\[
D_{\rm act}(X)=\sum_{q\le X+1\atop q\text{ prime}}\sum_{p<q\atop p\text{ prime}}
\left[
  1_{P(q-u_q(p))\le p}\,1_{p(q-u_q(p))\le X}
 -1_{P(u_q(p))\le p}\,1_{pu_q(p)-1\le X}
\right].                                                       \tag{20}
\]

On a good label, (20) is the boundary current of a 2-cycle: the two smoothness indicators are both 1 but the two cutoff indicators need not agree. On a bad label it is a truncated transient current. Estimate (5) controls bad incidences **after summing a complete fiber**, not these short cofactor windows. Summing its upper bound over `q<=X+1` would be much larger than X. The whole fibers `q<=sqrt X` cause only `O(X/log^3X)` signed error; the larger, truncated fibers are the issue.

Finally, the original signed counting function includes the inactive points `pq<=n+1` as well:

\[
D(X)=D_{\rm act}(X)+\sum_{n\le X\atop p(n)q(n)\le n+1}s(n)+O(1). \tag{21}
\]

Neither cancellation of the short-window current (20), nor its required aggregate cancellation with the inactive term, is proved here. A successful nonlocal contraction would need a new arithmetic comparison between the transported cofactor weights and **ordinary counting** at the destination scales. Full-fiber near-invariance alone supplies no such comparison. In particular it supplies no proof that a relative bias at one X persists over positive-logarithmic-density scales.

## Verification

`Submission/FiniteQReflectionVerification.py` checks the complete-fiber parametrization, the complement formula, monotonicity, the exact incoming-factor formula, the weighted degree identity, uniform finite-iterate l1 bounds, the natural-prefix escape implication, and the Selberg quadratic identity. These are finite computational checks of the algebra; (5) is proved analytically above, not inferred from numerical data. No Lean formalization of the analytic theorem is claimed.

The run passed 30,535 state/cofactor and incoming-factor checks, 4,300 finite-iterate l1 checks, 849,357 natural-prefix parity/escape checks, and 39 exact rational Selberg-weight checks. Independent direct sieving verified completeness for all 436 states with `q<=97`. For example, `q=19997` has 4,014 states, 390 transients, and 508 bad cofactor incidences.

The initial and final SHA-256 of `Submission/Spec.lean` is `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
