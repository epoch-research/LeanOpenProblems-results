# Selberg-weighted Titchmarsh continuation

## Status and scope

No proof or disproof of Erdős #5 was obtained. Spec.lean is unchanged and
neither of its declarations was used. This is a research derivation, not a
Lean formalization of the analytic number theory. The research agent's
read-only reports were independently checked at the principal algebraic
steps and against the cited source statements; this file preserves them.

The new variant is genuinely different from inserting an unproved hard
rough-cofactor mask: use an ordinary Selberg square on the shifted endpoint
and compute its correlation with the ordinary divisor function tau.
It supplies a computable mixed form on SHORT support. Its prime minorant
has the wrong sign throughout that support, with a sharp analytic threshold
at physical support radius 1/2. No extension to that threshold is proved.

## 1. Source input and the short-support reduction

Let L=log X, a be a nonzero even shift, and

    lambda_G(n)=sum_(d|n) mu(d) G(log d/L),
    G smooth on [0,infinity), supported in [0,rho], G(0)=1.

Initially take a fixed; the explicitly uniform BFI input permits a growing
logarithmic shift after checking the remaining elementary losses. The sums
in this section have NO CRT row and NO additional survivor weight.

Fouvry--Tenenbaum, `/corpus/src/2004.04766/BV-2021.tex`, lines 112--120,
explicitly restates the prime-specific BFI theorem:

    sum_(r<=R,(r,a)=1) |sum_(q<=U,(q,a)=1) Delta_prime(x;rq,a)|
       <<_A x/log^A x,

for R<=x^(1/10-epsilon), RU<=x/log^B x, and 1<=|a|<=log^A x. The outer
sum is absolute; the inner sum is SIGNED and UNWEIGHTED. This is not the
paper's general multiplicative-function exponent 1/105.

Fiorilli, `/corpus/src/1108.0439/1108.0439.tex`, lines 130--140 and 374--383,
derives the averaged linear-prime Titchmarsh theorem for

    sum_m Lambda(rm+a) tau(m),   r<=X^theta, theta<1/10.

IMPORTANT source correction: its displayed theorem omits (a,r)=1, but its
proof and the usable assertion require it. Taken literally at a=r=2 its
printed positive main term is false, since Lambda(2m+2) is supported only
on powers of 2. Its tau is tau(m), not tau(rm).

Divisor-bounded OUTER weights are allowed by Cauchy--Schwarz. If |xi_r| is
bounded by tau_K(r), then

    (sum tau_K(r)|E_r|)^2
       <= (sum tau_K(r)^2 |E_r|)(sum |E_r|).

The first factor is bounded trivially by (X+RU)log^C X, using nonnegative
prime counts and divisor moments; the second has arbitrary log saving.
This is the mechanism FT demonstrates at lines 549--572. It does not put
arbitrary weights in the inner q sum.

Expanding the Selberg square gives squarefree lcms ell<=X^(2rho), with
coefficients b_ell bounded by O_G(3^omega(ell)). The exact identity

    1_(ell|n) tau(n)
      = sum_(v|ell) mu(v) 2^omega(ell/v)
          1_(ell*v|n) tau(n/(ell*v))

has local verification k+2=2(k+1)-k. Thus the outer linear-prime coefficient
is r=ell*v, NOT ell alone. Keeping everything gives rho<1/40. Truncating
v<=X^eta improves the budget to

    2rho+eta < 1/10-epsilon,

and hence every fixed rho<1/20. The discarded tail is bounded in absolute
value by X^(1+o(1))/X^eta + X^(2rho+o(1)): writing ell=vt produces a
convergent v^(-2) tail. One must group the retained coefficients by r and
use the averaged theorem, not sum an individual Titchmarsh error X^(2rho)
times. Prime powers contribute only X^(1/2+o(1)).

For logarithmic a, Fiorilli's published theorem alone is not enough (it
fixes a). Its divisor-switching proof can use the explicitly uniform BFI
statement above; its other dependence on a, including 3^omega(a), endpoint
shifts and ordinary BV maxima over reduced residues, is logarithmic.
This is a derived extension, not a verbatim uniform theorem in Fiorilli.

With these reductions, the row-free main forms are

    sum_(X<n<=2X) 1_Prime(n+a) |lambda_G(n)|^2
      = S(a) X/L^2 (I(G)+o(1)),
    sum_(X<n<=2X) 1_Prime(n+a) tau(n) |lambda_G(n)|^2
      = S(a) X/L^2 (T(G)+o(1)),

where I(G)=integral |G'|^2 and

    T(G)=2 integral |G'|^2 + integral t(1-t)|G''|^2.       (A)

The usual two-prime singular series is

    S(a)=product_(p|a) (1-1/p)^(-1)
         product_(p not|a) (1-2/p)/(1-1/p)^2.

The next section derives (A), including the term lost by ignoring the
logarithmic derivative of the lcm coefficient.

## 2. Exact Euler deformation and the main form

Write D_p=p^2-p+1. For (q,a)=1,

    sum_(r,a)=1 r^(-w)/phi(qr) = zeta(1+w) H_q(w),
    H_q(w)=1/phi(q)
      product_(p not|aq) (1+p^(-1-w)/(p-1))
      product_(p|a) (1-p^(-1-w)).

The divisor-hyperbola residue for a cumulative sum is

    X{H_q(0)[log(X/q)+2gamma-1]+2H_q'(0)}.

In particular, both -log q and 2H_q'(0) matter. For squarefree ell package
this as

    A_tau(ell;z)=sum_(v|ell) mu(v)2^omega(ell/v)
                      (ell*v)^(-z) H_(ell*v)(2z).

The coefficient is X[(L+2gamma-1)A_tau(ell;0)+A_tau'(ell;0)].
For p not dividing a, set x=p^(-z). The exact local factors A_p,B_p are

    A_tau,p = 1+x^2/[p(p-1)],
    B_tau,p = (2x-x^2/p)/(p-1),

so A_tau(ell;z)=product_p A_p(z) product_(p|ell) B_p(z)/A_p(z).
At p|a take A_p=1-p^(-1-2z), B_p=0.

For example, at z=0,

    A_p=D_p/[p(p-1)],   B_p/A_p=(2p-1)/D_p,
    (A_p'/A_p)=-2log p/D_p,
    ((B_p/A_p)'/(B_p/A_p))
       =[-1+1/(2p-1)+2/D_p] log p.

The -log ell contribution is of leading size, not an O(1) correction.

Let U_p(s,t)=p^(-s)+p^(-t)-p^(-s-t). The EXACT double Mellin series of
Selberg coefficients has local factor

    E_p(s,t;z)=A_p(z)-B_p(z)U_p(s,t).

Extracting its polar part gives

    F(s,t;z)=H(s,t;z)
       zeta(1+s+t+z)^2 /
       [zeta(1+s+z)^2 zeta(1+t+z)^2].                  (B)

At the origin H=S(a). All three first logarithmic derivatives of H vanish.
This follows locally: E_p(0)/R_p(0) is the singular-series factor, and

    d_s log E_p = d_t log E_p = 0,
    d_z log E_p = 2log p/(p-1),

matching the local zeta quotient R_p. Thus

    F_z/F = 2[zeta'/zeta(1+s+t+z)
              -zeta'/zeta(1+s+z)-zeta'/zeta(1+t+z)]
            + H_z/H.

Take a smooth compactly supported extension of G to the whole real line,
with bilateral transform Ghat(s)=integral G(u)e^(su)du, and use vertical
inversion lines Re(s)=Re(t)=1. This extension is needed for rapid decay;
a one-sided transform need not decay rapidly when G(0) is nonzero.
Putting K(s,t)=s^2t^2/(s+t)^2, the bracket

    (L+2gamma-1)F(s/L,t/L;0)+F_z(s/L,t/L;0)

has leading value

    S(a)/L K(s,t)[1+2/s+2/t-2/(s+t)].                  (C)

The 2gamma term cancels the constants from logarithmic zeta derivatives.
For the contour functional against Ghat(s) conjugate-Ghat(t), Laplace
inversion yields

    I[s^j t^k/(s+t)^m]
      = (-1)^(j+k)/Gamma(m)
          integral u^(m-1) G^(j)(u) conjugate(G^(k)(u))du.

In particular,

    I[K] = integral u|G''|^2,
    I[K(1/s+1/t)] = integral |G'|^2,
    I[K/(s+t)] = (1/2) integral u^2|G''|^2.

Applying these identities to (C) gives (A). The boundary in the middle
identity vanishes at zero because of its factor u and at the upper end
because G is smooth and compactly supported.

For fixed a,G this contour passage can be justified without moving through
zeta zeros. On scaled Re(s)=Re(t)=1/L, absolute Euler products bound F by
O_a(L^6) and F_z by O_a(L^7). Truncate the unscaled contours at L^(1/4);
rapid transform decay makes the tails smaller than any prescribed power
of L. In a fixed small polydisc the regular Euler factors and derivatives
converge absolutely (remainders O(p^(-2+6eta))). Laurent expansions are
uniform on the retained contours; Re(s+t)=2 controls the diagonal. Finite
Euler factors at primes dividing a must additionally be tracked for growing
a. A family G_X would require uniform high derivative/transform seminorms;
this calculation does not grant them.

## 3. Squarefree insertion is an exact local cancellation

The identity mu^2*tau = h*tau, where multiplication on the left is pointwise,
has

    h(p^2)=-3, h(p^3)=2, h(p^j)=0 for other positive j.

It follows from (1+2z)(1-z)^2=1-3z^2+2z^3. Its absolute Dirichlet series
converges to the right of 1/2. Truncating its powerful-number convolution
at X^eta gives a power-saving tail and only adds O(eta) to the outer support
budget. This is not deletion by an unweighted squarefree-density estimate.

For this weight the deformed factors become

    A_sf,p=1-2x^2/[p(p-1)]+2x^3/[p^2(p-1)],
    B_sf,p=2x(1-x/p)^2/(p-1).

Writing J_p(z)=-3x^2/[p(p-1)]+2x^3/[p^2(p-1)], the exact identity is

    E_sf,p-E_tau,p = J_p(z)(1-U_p(s,t))
                  = J_p(z)(1-p^(-s))(1-p^(-t)).         (D)

Thus the singular series and leading derivative form are unchanged. At
s=t=z=0 the fixed-prime survival factor is 1-2/p, for both weights, not
that factor times a separate squarefree density. The corresponding ordinary
sieve-square insertion uses mu^2(n)=sum_(k^2|n)mu(k).

A simpler sufficient prime minorant does not need this stronger squarefree
asymptotic. The only composite n with tau(n)<4 are prime squares, so

    1_Prime(n) >= 2-tau(n)/2 -(1/2)1_(n is a prime square)

for n>1. The prime-square contribution after Selberg weighting is only
X^(1/2+o(1)).

## 4. Sharp variational threshold

The minorant's principal quadratic form is

    M(G)=2I(G)-T(G)/2
        = I(G)-(1/2) integral t(1-t)|G''|^2.             (E)

Let f=-G', h(t)=1-2t. For rho<=1/2 the ground-state identity

    integral t(1-t)|f'|^2 - 2 integral |f|^2
      = integral t(1-t)h(t)^2 |(f/h)'|^2 >=0

follows by integration by parts from -(t(1-t)h')'=2h. Boundary terms vanish;
at rho=1/2 take the endpoint limit. Thus M<=0 throughout this range.

At rho=1/2 equality is attained in the Sobolev closure by G=(1-2t)_+^2.
For rho>1/2, the explicit quadratic G_r(t)=(1-t/r)_+^2 with 1/2<r<rho has

    I=4/(3r),
    integral t(1-t)|G_r''|^2=2/r^2-4/(3r),
    M=(2r-1)/r^2>0.

Smooth approximation preserves the strict inequality. Hence positivity of
this FUNCTIONAL is possible exactly for rho>1/2. This is not a claim that
the arithmetic formula is established on that support. The proven
short-support reduction is only rho<1/20, far from the threshold.

For r=1/4 the quadratic test has T-4I=16; at r=3/5 it has M=5/9. These are
checks on the analytic formula, not prime-pair counts.

## 5. CRT and exceptional terms do not close the gap

For endpoints n,n+a on a reduced row n=b mod Q, define the actual residue
A_Q(m) by

    A_Q(m)=a mod m,    A_Q(m)=b+a mod Q,   (m,Q)=1.

It DEPENDS ON m. Expanding the divisor hyperbola and the Selberg square
produces errors on moduli Q[ell,q], with ell<=X^(2rho), q<=sqrt(2X), and
this varying residue. Using theta for prime logarithmic weights, an exact
version has q-dependent interval lower endpoint max(X,q^2-1):

    2 sum_ell b_ell sum_q
       {theta(2X+a;Q[ell,q],A_Q([ell,q]))
        -theta(max(X,q^2-1)+a;Q[ell,q],A_Q([ell,q]))
        -(2X-max(X,q^2-1))/phi(Q[ell,q])}.

The usual coprimalities with Qa apply; the square correction is
X^(1/2+o(1)). The switched form still has varying CRT residues and is NOT
the fixed-residue BFI theorem merely with Q absorbed into r.

The natural prime-count benchmark is S_Q(a) X/(Q log^2 X), where

    S_Q(a)=product_(p|Q)(1-1/p)^(-2)
            product_(p not|Q)(1-nu_p(a)/p)/(1-1/p)^2.

An error X/log^A X has relative size Q log^(2-A)X/S_Q(a).
Q=X^o(1) does not make this small. A periodic-modulus loss Q^C worsens it.
BFM's smooth-modulus modified BV does supply a real 1/phi(Q) saving and a
maximum over residues, but only below its stated total-modulus level;
it does not by itself cover this weighted Titchmarsh aggregate. No such
CRT-relative estimate, nor the required long-support structured combination
of errors, was obtained.

Nor can the favorable sign of an UNWEIGHTED exceptional-zero term be
silently kept after Selberg weighting. At a prime conductor r not already
in the fixed modulus, the exceptional restriction on divisor indices
1,r gives, up to a positive scalar and character sign, the Gram block

    [[0,1],[1,1]],

which has determinant -1. Absorbing Mobius signs leaves it indefinite.
Including divisor terms already divisible by r adds an all-ones matrix;
the resulting determinant is still -beta(alpha+beta)<0 when the missing-r
part beta is positive. If the entire conductor is already fixed, that
particular example does not apply. Excluding r from sieve divisors alone
does not exclude it from the ordinary Titchmarsh divisor variable.

Additional sources checked by the research agent:
- Drappeau--Topacogullari 1807.09569, divtm-alpha.tex 51--73, 84--92,
  870--904: fixed prime-periodicity and ordinary divisor on the opposite
  side, not freely weighted shifted prime linear forms.
- Assing--Blomer--Li 2005.13915, 2005.13915.tex 79--89, 124--131,
  687--695, 735--747: unconditional extra congruences only polylogarithmic;
  power-sized variants/power-saving require GRH as stated.
- BFM 1404.5094, 694--715 and 786--809: actual exceptional-prime exclusion
  and modified BV, not a weighted-Titchmarsh replacement.

No simultaneous prime endpoints or consecutive-gap limit follows from
this continuation. Spec remains at its original two sorry proofs.
