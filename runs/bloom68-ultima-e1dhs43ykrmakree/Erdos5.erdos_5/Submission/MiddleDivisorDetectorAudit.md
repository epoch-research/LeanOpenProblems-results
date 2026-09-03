# An exact middle-divisor prime detector and its variational obstruction

## Status and scope

Erdős #5 is unresolved. No analytic prime-correlation theorem is asserted
here. `Spec.lean` was not edited, imported, or used. This audit independently
derives the elementary detector, a smooth replacement, an exact finite
combinatorial expansion, and a **rigorous finite arithmetic coefficient
model**. In that model the improved detector still has a strictly negative
main quadratic form for every fixed `0 < eta < rho <= 1/2`, `eta <= 1/3`.
There is also a sharp constrained optimization, not just an equivalent
positivity criterion.

The previous `WeightedTitchmarshAudit.md` was read. Its Titchmarsh/BFI
assertions are **not** used to derive the new mixed coefficient below.
In particular, an asymptotic for the actual prime-weighted sum must still
be proved separately. Extending the coefficient calculation to support
where progression-density replacement is unjustified is not an analytic
number-theory theorem.

## 1. Exact classification, including equality cases

Fix `n > 1` and `0 < eta <= 1/3`, and put

    A = n^eta, B = n^(1-eta),
    D_eta(n) = #{d | n : A < d < B}.

### No middle divisor

If `D_eta(n) = 0`, exactly the following possibilities occur:

1. `n = P m`, where `P` is prime, `P >= B`, `m <= A`, and `(P,m)=1`;
   `m=1` is allowed precisely when `n` is prime.
2. `eta=1/3` and `n=p^3` for a prime `p`.

The alternatives are disjoint. Thus the proposed strict inequality `P>B`
is false at a genuine endpoint, and the prime cube is a genuine exception
to the proposed factorization. Neither invalidates the detector.

Proof: If some prime factor `P>A`, absence of middle divisors implies
`P>=B`. Since `B>sqrt(n)`, its exponent is one, `m=n/P<=A<P`, and it is
coprime to `m`. Otherwise all prime factors are at most `A`. Multiply prime
factors with multiplicity until the first product `d>A`. Then

    A < d <= A^2 <= B.

Absence of a middle divisor forces equality throughout the last two
inequalities: `eta=1/3`, the last prime factor is `A`, and the preceding
product is also `A`. Consequently `A=p` is prime and `n=p^3`.
The converse in both alternatives follows directly by separating divisors
of `m` from divisors containing `P`, or by listing divisors of `p^3`.

### Parity and the one-middle-divisor cases

Complementation `d -> n/d` preserves the strict middle interval. It has a
fixed point if and only if `n` is a square, and that fixed point is always
inside the interval. Hence

    D_eta(n) == 1_(n is a square)  (mod 2).

In particular, a nonsquare with a nonempty middle interval has at least
two middle divisors, even if it has repeated prime factors.

There is also a complete classification of `D_eta(n)=1`:

    n=p^2; or
    n=p^4 and eta>=1/4; or
    n=p^6 and eta=1/3.

Proof: Write `n=s^2`. If it is not a prime square, every prime factor is
less than `s` and hence at most `A`. If distinct primes `q<p` divide `s`,
then `s/q<s`, so `s/q<=A` and `q>=s/A`. The integer `s q/p` is a divisor
of `n`, is less than `s`, and satisfies

    s q/p >= n/A^2 >= A.

Since no divisor other than `s` is middle, all these inequalities must be
equalities. This gives `eta=1/3`, `p=A`, `q=s/A`, and `p=q^2`, impossible
for primes. Thus `n=p^(2k)`. Listing its divisors gives the stated cases.

More generally, for every prime power `n=p^k`,

    D_eta(p^k) = k - 2 floor(k eta) - 1,
    lambda_G(p^k) = 1 - G(1/k).

The floor formula includes equality endpoints, not just generic eta.

## 2. Precise detector theorems

Let `G:[0,infinity)->R` be smooth, equal to one on `[0,eta]` and zero on
`[rho,infinity)`, where

    0 < eta < rho < 1/2, eta <= 1/3.

No monotonicity or sign condition on `G` is needed. Define, with the
**actual** denominator `log n`,

    lambda_G(n) = sum_(d|n) mu(d) G(log d / log n).

For a prime, `lambda_G=1`. For a composite with `D_eta=0`, it vanishes:

- In case 1 above, every divisor containing `P` is outside the support,
  and every divisor of `m` is on the plateau. Thus

      lambda_G(n) = sum_(d|m) mu(d) = 0, since m>1.

  This is valid for nonsquarefree `m` and for `P=B`, `m=A`.
- For the exceptional cube, `lambda_G(p^3)=1-G(1/3)=0`.

For `D_eta=1`, the fourth- and sixth-power exceptions also have lambda
zero, whereas a prime square has lambda one. Therefore the following is
an **exact**, not asymptotic, prime minorant for every integer `n>1`:

    lambda_G(n)^2 (1 - D_eta(n)/2)
        - (1/2) 1_(n is a prime square)
      <= 1_(n is prime).                                      (1)

It equals one at every prime. The prime-square correction is necessary:
the uncorrected expression equals `1/2` at every prime square.

An even simpler all-case version uses the unordered count

    C_eta(n) = #{d|n : n^eta < d <= sqrt(n)}
             = (D_eta(n) + 1_(n is a square))/2.

Then

    lambda_G(n)^2 (1 - C_eta(n)) <= 1_(n is prime).              (2)

Both formulas cover all repeated factors and all endpoint equalities.
There is no need to claim that equality endpoints are negligible. The
only logarithmic singularity is `n=1`, which was excluded. At divisor
endpoints `d=1,n`, the normalized logs are exactly `0,1`, with values
`G(0)=1` and `G(1)=0`.

The restriction `eta<=1/3` is sharp for this construction in general.
For `n=101*103*107=1113121`, `eta=17/50>1/3`, and `rho=2/5`, each prime
factor is below `n^eta` and every product of two is above `n^(1-eta)`.
Thus `D_eta=0` but `lambda_G=1-3=-2` for **every** such plateau/cutoff G.

If desired, the hard definition at `eta=0` reduces to the old detector:
`D_0=tau-2`. But the smooth construction below uses a strictly positive
eta, and the present optimization imposes a nontrivial plateau.

## 3. Honest smooth divisor weights

Choose any `v in C_c^infinity((0,1))` with `v>=0` and

    v(t)>=1 for eta<=t<=1/2.

For example, take `v=1` on this interval, with a smooth rise from zero
below eta and a smooth fall to zero above 1/2. Then

    V_v(n) = sum_(d|n) v(log d/log n) >= C_eta(n),

including at a square root. Consequently

    lambda_G(n)^2 (1 - V_v(n)) <= 1_(n is prime)                (3)

is a completely smooth-divisor-weighted, exact detector, with **no
square correction or endpoint exception**. At a prime `V_v=0`.
This is a majorant of the unordered divisor penalty, not a smoothing
from below. Transitions can be made arbitrarily thin while fixed in X.

Another useful option is a symmetric smooth `w>=0`, supported in `(0,1)`,
with `w=1` on `[eta,1-eta]`. Then

    lambda_G(n)^2 [1 - (sum_(d|n) w(log d/log n)
                             + 1_(n is a square))/2]
      <= 1_(n is prime).                                      (4)

One may replace its all-square correction by the prime-square correction
in (1), by the `D=1` classification. Both are exact.

**A tempting but false smoothing.** If `0<=G<=1`, put
`w(t)=1-G(t)-G(1-t)`. On a semiprime `n=pq`, with
`eta<t=log p/log n<rho` and `0<G(t)<1`,

    lambda_G=1-G(t), sum_(d|n) w(t_d)=2(1-G(t)).

The proposed product minorant would then equal
`G(t)(1-G(t))^2>0` at a composite. An arbitrarily small positive gap is
still a false pointwise lower bound. Smooth cutoffs must majorize the
necessary penalty, not merely approximate it in measure.

The difference between (1) and (2) is supported on squares and is bounded
in absolute value by `O_G(tau(n)^2)`. On `X<=n<=2X` its total is
`O_(G,epsilon)(X^(1/2+epsilon))`, even after multiplication by a prime
indicator. This follows from the elementary divisor bound; no unweighted
square-density argument for a different weight is being substituted.

## 4. Moving log n: a genuinely safe freezing rule

Blindly replacing `log n` by the lower dyadic endpoint `log X` is false
pointwise. For example, `eta=1/3`, `n=27`, and `X=20` give `D_eta(n)=0`,
but `log 3/log 20>1/3`; a G which immediately leaves its plateau can give
`lambda_(G,X)(27)>0`.

There is an exact alternative. Let `1<X<=n<=Y`, and suppose

    Y^rho <= sqrt(X),   sqrt(Y)<X.                            (5)

Both hold eventually for fixed rho<1/2 and bounded `Y/X`. Set

    lambda_(G,Y)(n)=sum_(d|n) mu(d) G(log d/log Y).

For a no-middle-divisor composite, its small cofactor satisfies
`m<=n^eta<=Y^eta`, while the dominant prime satisfies
`P>=n^(1-eta)>sqrt(X)>=Y^rho`. Thus the cancellation proof survives
unchanged. The prime cube is also on the plateau. Primes still have
lambda one. Hence (2) is valid with this **upper-endpoint-frozen** lambda.

Moreover the entirely fixed count

    C_(X,Y)(n) = #{d|n : X^eta < d <= sqrt(Y)}

majorizes `C_eta(n)` and vanishes on primes in the window. Therefore

    lambda_(G,Y)(n)^2 (1 - C_(X,Y)(n)) <= 1_(n is prime)         (6)

is exact. This freezes both G and the divisor interval without dishonest
pointwise errors, at the cost of harmless additional negative values.
With `L=log Y`, the lower logarithmic cutoff is
`eta log X/log Y = eta+O(1/L)`, and the upper one is exactly `1/2`.
This provides a legitimate fixed-scale expression for the coefficient
calculation below. It does not presume a uniform moving-G asymptotic.

## 5. Exact finite lcm/gcd decomposition

This identity is available before making any analytic approximation.
For arbitrary finitely supported real coefficients `c_d`, set

    lambda(n)=sum_(d|n) c_d,
    b_ell=sum_([d,e]=ell) c_d c_e.

Then `lambda(n)^2=sum_(ell|n) b_ell`. For the Mobius-G coefficients,
`ell` is squarefree,

    |b_ell| <= ||G||_infinity^2 3^omega(ell),
    ell <= exp(2 rho L)

on a frozen scale L.

For **any** divisor weight `F_n(k)` one has the exact identity

    1_(ell|n) sum_(k|n) F_n(k)
      = sum_(r|ell) sum_(q>=1, (q,ell/r)=1)
            F_n(rq) 1_(ell q|n).                              (7)

Indeed take `r=(k,ell)`, `q=k/r`; then `[k,ell]=ell q`. Thus, for example,

    lambda_G(n)^2 C_eta(n)
      = sum_ell b_ell(G;n) sum_(r|ell)
          sum_(q>=1, (q,ell/r)=1,
                         n^eta<rq<=sqrt(n)) 1_(ell q|n).        (8)

Here `b_ell(G;n)` has the actual moving denominator, or one may use frozen
coefficients and the fixed interval in (6). Removing the coprimality by
Mobius inversion gives

    sum_(r|ell) sum_(s|ell/r) mu(s)
          sum_(v>=1) F_n(rsv) 1_(ell s v|n).                   (9)

This displays exactly where the shifted divisor cutoff and the enlarged
outer modulus `ell s` arise. The inner sum is not automatically the
unweighted inner sum from some distribution theorem. When `F=1`, summing
over r gives the previous tau identity with coefficient
`mu(s) 2^omega(ell/s)`. For the new cutoff the r-dependence cannot be
silently removed.

Equivalently, before the gcd split the moving middle count imposes the
exact n-interval `k^2<=n<k^(1/eta)` and modulus `[d,e,k]` on the expanded
sum. The strict upper bound is important at equality endpoints.

## 6. Independently derived finite progression-density model

Fix a nonzero even integer a and `L -> infinity`. For smooth compactly
supported H on `[0,infinity)` define the **finite arithmetic sum**

    Q_H(L;G) = sum_(k,d,e >=1, (kde,a)=1)
        H(log k/L) mu(d)mu(e) G(log d/L)G(log e/L)
        / phi([k,d,e]).

Also define `I_L(G)` by fixing `k=1` and omitting H. These are arithmetic
coefficient sums, not prime-counting asymptotics. Write

    S(a)=product_(p|a) (1-1/p)^(-1)
         product_(p not|a) (1-2/p)/(1-1/p)^2,
    I(G)=integral_0^infinity G'(t)^2 dt,
    q_G(u)=integral_0^infinity min(t,u) G''(t)^2 dt.

Then the following coefficient asymptotics are rigorous:

    I_L(G) = S(a)/L [I(G)+o(1)],
    Q_H(L;G) = S(a)/L [H(0) I(G)
                        + integral_0^infinity H(u) q_G(u) du
                        + o(1)].                             (10)

Thus the limiting divisor-state measure has an atom `I(G)` at zero and
the nonnegative, increasing, concave density `q_G(u)` thereafter. It
becomes constant for `u>=rho`.

### Derivation, not an imported mixed formula

The exact triple Dirichlet series has local factor, for `p not|a`,

    U_p=p^(-s)+p^(-t)-p^(-s-t),
    E_p(s,t,u)=1-U_p/(p-1)
              +(1-U_p) p^(-u)/[(p-1)(1-p^(-1-u))].            (11)

The first part has `p not|k`; the second sums all positive valuations of
k. At `p|a` the factor is one. Extracting the first-order Euler factors
therefore gives the exact factorization

    F(s,t,u)=H_a(s,t,u)
      zeta(1+s+t) zeta(1+u) zeta(1+s+t+u)
      / [zeta(1+s) zeta(1+t) zeta(1+s+u) zeta(1+t+u)],          (12)

where `H_a` is analytic in a fixed neighborhood of zero, its Euler
remainders are absolutely convergent there, and `H_a(0,0,0)=S(a)`.
After scaling the variables by L, its leading rational kernel is

    K(s,t,u)=s t (s+u)(t+u)/[u(s+t)(s+t+u)]
            = s t/(s+t)
                + s^2 t^2/[(s+t)u(s+t+u)].                    (13)

This algebraic decomposition is especially useful. Inversion in u gives
an atom from the first term and, from the second, the kernel

    s^2 t^2/(s+t)^2 [1-exp(-(s+t)u)].

Double inversion against G turns it into

    integral t G''(t)^2 dt
       - integral_(t>=u) (t-u) G''(t)^2 dt = q_G(u).

The atom becomes `I(G)`. For `I_L` itself, the exact Euler factor is
`1-U_p/(p-1)`; its polar quotient is
`zeta(1+s+t)/(zeta(1+s)zeta(1+t))`, with scaled kernel `st/(s+t)`.
This separately verifies its claimed leading term and proves the
functional in (10).

For rigor, use compactly supported smooth extensions of G and H to the
whole real line and bilateral Mellin/Laplace inversion on positive
vertical lines. Their transforms decay faster than every power. On the
scaled positive lines the absolute Euler products have polynomial-log
bounds (a bound `O_a(L^C)` for a fixed C suffices). Truncate the unscaled
contours at a small power of L, use the uniform Laurent expansions of
zeta and the absolutely convergent regular Euler product near the origin,
and bound the tails by rapid transform decay. No contour through zeta
zeros, prime-distribution assertion, or moving family of unbounded
seminorms is needed.

### Sharp divisor cutoffs are also justified

Let `Q_alpha` be the same finite sum with `k<=exp(alpha L)`. For every
fixed `alpha>0`, smooth upper/lower approximations yield

    Q_alpha(L;G)=S(a)/L [I(G)
        + integral K_alpha(t) G''(t)^2 dt + o(1)],

    K_alpha(t)=alpha t-t^2/2+(t-alpha)_+^2/2.                   (14)

The squeeze is legitimate despite the Mobius signs. For fixed k the
kernel `1/phi([k,d,e])`, with the indicated coprimality restrictions, is
positive semidefinite: take M to be a common multiple of all indices and
choose `b` uniformly among the units modulo M. Then

    Prob([k,d,e] divides b-a)=1/phi([k,d,e]).

The quadratic coefficient is exactly the expectation of a square times
`1_(k|b-a)`. Consequently `Q_H` is monotone in a nonnegative divisor
weight H. The limiting density in (10) is continuous away from zero,
which completes the sharp-cutoff squeeze, including cutoff equalities.
It also handles `alpha=eta+O(1/L)` from (6).

This coefficient theorem is valid for every fixed support radius, but
replacing an actual prime sum by these coefficients is a **separate
analytic issue**. In particular, when lcms exceed the summation interval,
individual progression-density replacements are not valid. No such
long-support replacement is being claimed here.

## 7. The improved functional, and why its sign still fails

For the exact frozen-window detector (6), the progression-density main
coefficient is

    I_L(G) - Q_(1/2)(L;G) + Q_(eta+O(1/L))(L;G).

Since `G''=0` on `[0,eta]` and on `[rho,infinity)`, and `rho<=1/2`, (14)
gives

    Q_eta : I(G) + (eta^2/2) integral G''(t)^2 dt,
    Q_(1/2) : I(G) + (1/2) integral t(1-t) G''(t)^2 dt.

The resulting principal functional is therefore

    M_eta(G)=I(G)
       - (1/2) integral_eta^rho [t(1-t)-eta^2] G''(t)^2 dt.     (15)

In particular, the middle-divisor modification genuinely improves the
old tau functional, for the same G, by

    (eta^2/2) integral G''(t)^2 dt.

This was derived from (11)-(14), not by citing a new BFI mixed formula.
As a check, twice the `Q_(1/2)` form recovers
`2I+integral t(1-t)G''^2` on this support.

But put

    f=-G', a_eta(t)=t(1-t)-eta^2, h(t)=1-2t.

Here `f(eta)=f(rho)=0`, `integral f=1`, `a_eta>0`, and

    -(a_eta h')'=2h.

For `rho<1/2`, integration by parts gives the exact ground-state identity

    integral a_eta f'^2 - 2 integral f^2
       = integral a_eta h^2 ((f/h)')^2.                       (16)

All boundary terms vanish. At `rho=1/2` it follows by endpoint limits
for the smooth flat functions, and then by Sobolev closure. This is the
endpoint of the coefficient/variational calculation; the dyadic freezing
rule (5) itself requires `rho<1/2` when `X<Y`. Consequently

    M_eta(G) = -(1/2) integral a_eta h^2 ((f/h)')^2 < 0         (17)

for every admissible G and every fixed `0<eta<rho<=1/2`. Equality would
force `f=c h`, incompatible with `f(eta)=0` and `integral f=1`.
The plateau needed for exact cancellation prevents the putative gain
from changing the sign.

There is a simple comparison with the old functional as well. For
`J(u)=G(u+eta)` and `R=rho-eta`,

    a_eta(t)=(t-eta)(1-(t-eta))+eta(1-2t),

so, on this support,

    M_eta(G) <= M_0(J) <= (2R-1)/R^2 < 0.                    (18)

The last inequality is sharp for the old unconstrained form, with
Sobolev optimizer `J(u)=(1-u/R)_+^2`; it follows by completing the
quadratic form around that function. This is a variational domination,
not a false claim that the new detector is pointwise below the old tau
detector. In fact, before square corrections,

    lambda^2(1-D_eta/2)
      = lambda^2(2-tau/2) + lambda^2(A_eta-1),
    A_eta=#{d|n:d<=n^eta},

so its pointwise improvement is real and nonnegative.

For the smooth detector (3), complementing divisors gives the effective
short-divisor weight `v(u)+v(1-u)` on `[0,1/2]`, up to an explicit
square-supported term. This weight is at least one on `[eta,1/2]` and
nonnegative elsewhere. Its limiting penalty is

    integral_0^(1/2) [v(u)+v(1-u)] q_G(u) du
       >= integral_eta^(1/2) q_G(u) du.

Thus its main form is no larger than (15). The same conclusion holds for
(4). Honest smoothing cannot reverse the sign; it can approach the hard
form from below as its transition widths tend to zero.

## 8. Sharp constrained optimum: an explicit dual calculation

For fixed `0<eta<rho<1/2`, define

    A0=integral_eta^rho 1/(a_eta h^2),
    B0=integral_eta^rho 1/h^2,
    C0=integral_eta^rho a_eta/h^2,
    S_eta,rho=C0-B0^2/A0 > 0.

In the closure `f in H_0^1(eta,rho)`, `integral f=1`, the **exact** optimum
is

    sup_G M_eta(G) = -1/(2 S_eta,rho).                         (19)

To see this directly, set `b=a_eta h^2` and let v satisfy

    v(eta)=v(rho)=0,
    b v' = B0/A0-a_eta.

Then `-(b v')'=h`,

    integral h v = integral b v'^2 = S_eta,rho.

For `w=f/h`, integration by parts and Cauchy--Schwarz give

    1=integral h w=integral b v'w',
    integral b w'^2 >= 1/S_eta,rho.

Equality holds for `w=v/S_eta,rho`. The optimizer is positive in the
interior, so allowing oscillatory G does not improve the optimum. Smooth
flat G approximate it in the requisite Sobolev norm. This is an evaluated
dual bound, not merely a reformulation of a positivity question.

At the endpoint `rho=1/2`, put

    c=sqrt(1-4eta^2), h0=1-2eta.

The limiting formula is especially simple:

    S_eta,1/2 = [c artanh(h0/c)-h0]/8,
    sup_G M_eta(G) = -4/[c artanh(h0/c)-h0] < 0.               (20)

For example:

    eta=0.1, rho=0.4:  sup M = -30.1033817341,
    eta=0.1, rho=0.5:  sup M = -12.3816939925,
    eta=1/3, rho=0.5:  sup M = -157.848311971.

An unnormalized endpoint optimizer is

    f0(t)=h(t)/(2c) * [artanh(h0/c)-artanh(h(t)/c)],

with `integral f0=S_eta,1/2`. As `eta -> 0` for fixed `rho<1/2`, (19)
tends to `(2rho-1)/rho^2`, recovering the old sharp quadratic optimum.
At `rho=1/2`, the optimum approaches zero only as the plateau shrinks to
zero; it is strictly negative for every fixed positive plateau.

## 9. Verification and conclusion

`check_middle_divisor_detector.py` independently checks:

- 99,995 pointwise cases, all `2<=n<=20000`, at five rational eta values,
  enforcing endpoint comparisons by integer powers;
- the full `D=0` and `D=1` classifications, repeated factors, prime powers,
  prime-square correction, unordered and smooth detectors;
- exact frozen-window detectors, including eta=1/3;
- the exact lcm/gcd expansion for 499 integers;
- the polar-kernel algebra, ground-state and Legendre identities;
- an exact finite residue-space realization of the positive kernel;
- numerical quadrature of the sharp optima, and a genuinely C-infinity
  test function checking both (16) and the divisor-density integral;
- explicit failures for eta>1/3, naive smoothing, and lower-endpoint
  freezing.

All checks passed. These computations supplement, not replace, the
proofs above. `Spec.lean` SHA-256 before/after this work is
`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.

**Conclusion.** The proposed detector can be repaired completely, and
there is an exact smooth version with no pointwise gaps. Its short-divisor
improvement is real. Nevertheless the independently derived finite
progression-density main coefficient is governed by (15), whose sharp
optimum is strictly negative throughout `rho<=1/2` for every positive
plateau. Thus this modification does not remove the previous radius-1/2
sign obstruction within that model. Establishing actual prime-weighted
mixed asymptotics, or finding additional arithmetic effects not represented
by these local coefficients, remains a separate problem. No simultaneous
prime endpoints or resolution of Erdős #5 follows.
