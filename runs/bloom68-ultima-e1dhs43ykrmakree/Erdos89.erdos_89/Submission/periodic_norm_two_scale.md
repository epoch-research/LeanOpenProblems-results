# Actual two-scale contraction for every fixed periodic Gaussian mask

## Result and scope

**The proposed fixed-mask limit is true.** This note proves the necessary
regularity for the **actual** norm population, including orientation failures.
It does not replace actual distances by local capacity. There is also a genuine,
but only eventual fixed-modulus, finite-endpoint contraction below. The sharp
planar distinct-distance problem and unrestricted contraction remain unresolved.

Use the notation and the audited theorem of
`periodic_norm_support_audit.md`. Thus, with O=Z[i], fix M>=1 and a nonempty
A subset O/(M), and put

    B=A-A,   delta=|A|/M^2,
    P_R=(A+MO) intersect closedDisk(0,R),
    n_R=|P_R|,   K(P)=|P|/D(P),
    F_B(X)=#{1<=m<=X : N(z)=m for some z reducing to B}.

D counts distinct positive distances, equivalently squared distances. Write
kappa for the Landau--Ramanujan constant and lambda=lambda_B for the audited
local norm probability. The previously proved inputs are

    lambda>=delta>0,                 F_B(X)~kappa lambda X/sqrt(log X),
    n_R=pi delta R^2+O_M(R+1),       D(P_R)=F_B(4R^2)+O_M(R+1).    (0.1)

Constants here and below can be made uniform over A for a fixed M.

### Theorem

For every fixed M,A and every fixed 0<t<1,

    K(P_R)^2-K(P_(tR))^2
       -> (pi delta/(4 kappa lambda))^2 log(t^(-2)).              (0.2)

In particular the answer to the question with t=1/2 is

    lim [K(P_R)^2-K(P_(R/2))^2]
       = (pi delta/(4 kappa lambda))^2 log 4
       <= C_4 := (pi/(4 kappa))^2 log 4 = 1.46417931966... .      (0.3)

The universal limiting bound is sharp, already for M=1, and also for singleton
masks at any M. All limits use actual D at both scales.

The conclusion is NOT that F_B differs from local capacity by
O_M(X/(log X)^(3/2)). That assertion remains false. In fact Section 7 sharpens
the saved mod-13 example to a missing population of order X/(log X)^(5/6).
Its squared-potential capacity deficit grows like a positive multiple of
(log X)^(2/3), while (0.3) still holds.

## 1. An exact finite multiplicative state, not a multiplicity weight

Let U be the image of {1,-1,i,-i} in O/(M). Let T be the finite set of U-orbits
of O/(M), with its well-defined commutative multiplication. It includes
nonunit and zero orbits. Let S be the finite monoid of all **nonempty subsets**
of T, with setwise multiplication and identity {1_T}.

For an integer m represented by a Gaussian norm, let

    W(m)={the U-orbit of z mod M : N(z)=m} in S.

Let E=C[S] be the finite-dimensional monoid algebra, with basis e_V, V in S,
and product e_V e_W=e_(VW). Its coefficient l1 norm is submultiplicative and
||e_V||=1. Define an E-valued arithmetic function

    a(m)=e_(W(m)) if m is a positive Gaussian norm, and a(m)=0 otherwise.

A nonempty state consisting of the zero residue is retained; it is not the
zero vector of the algebra, which is reserved here for nonnorm integers.

Unique factorization in O gives a(mn)=a(m)a(n) when gcd(m,n)=1: the Gaussian
prime factors over the disjoint rational prime divisors can be assigned to the
two factors separately. This remains true when one side is zero, by the even
valuation criterion at inert primes. In particular ||a(m)||<=1.

For a split prime p=pi_p conjugate(pi_p), writing c for the orbit of pi_p,

    W(p^k)={c^j conjugate(c)^(k-j): 0<=j<=k}.                    (1.1)

For p=3 mod 4, only even powers are norms and
W(p^(2k))={orbit(p)^k}. Also W(2^k)={orbit(1+i)^k}. These formulas are valid
at primes dividing M as well; no unit assumption is made there.

Define a linear functional l_B on E by

    l_B(e_V)=1 if some orbit in V meets B, and 0 otherwise.

Then l_B(a(m)) is **exactly the indicator counted by F_B**. Global unit
multiples of every representation are available, so meeting B is the right
acceptance test. In particular no representation multiplicities enter. The
functional l_B is generally not multiplicative: scalar Selberg--Delange
cannot be applied directly to F_B as if it were a multiplicative function.

## 2. The algebra-valued Euler product and its singular exponent

Put

    G=(O/(M))^*/U,       g=|G|,
    w(c)=e_({c,conjugate(c)}) for c in G,
    V=(1/(2g)) sum_(c in G) w(c) in E.                           (2.1)

Here G embeds in T, and conjugation is well defined. Since O is a PID, G is
its ray class group modulo (M): a prime ideal coprime to M has the class of
any Gaussian generator modulo M, modulo U. Either reciprocal convention for
ray classes gives the same argument if used consistently.

For Re(s)>1 the series and Euler product

    D(s)=sum_(m>=1) a(m)m^(-s)=product_p sum_(k>=0) a(p^k)p^(-ks) (2.2)

converge absolutely in E. After removing finitely many small primes, the
logarithm of a local factor is

    w(c_p)p^(-s)+O(p^(-2 Re(s)))     at split p not dividing 2M,
    O(p^(-2 Re(s)))                 at inert p.

The errors sum normally for Re(s)>1/2. Indeed the coefficients have norm at
most one, and for all sufficiently large p the local factor is within a
fixed radius less than one of the algebra identity. The omitted finite Euler
factors are holomorphic for Re(s)>0; they need not be inverted or logarithmed.

Since w(c)=w(conjugate(c)), counting the two prime ideals above a split
rational prime gives

    sum_(split p not dividing 2M) w(c_p)p^(-s)
      = (1/2) sum_(prime ideals q coprime to M) w(c_q)N(q)^(-s)
          + an E-valued function holomorphic for Re(s)>1/2.      (2.3)

The degree-two prime ideals and the finitely many omitted ideals have been
absorbed in the holomorphic term. Fourier expansion on G now gives

    D(s)=E_0(s) exp( sum_(chi in G-hat) V_chi log L_O(s,chi)),
    V_chi=(1/(2g)) sum_(c in G) w(c) conjugate(chi(c)),            (2.4)

where E_0 is E-valued and holomorphic for Re(s)>1/2. For example, to derive
(2.4), replace each prime-ideal character sum by log L_O(s,chi); the difference
is the normally convergent sum of prime-power terms of degree at least two.
All operations commute because E is commutative. The principal V_chi is V.

### Precise analytic input

For the finitely many fixed finite-order Hecke characters in (2.4), standard
unconditional Hecke L-function theory provides a c_M>0 such that on

    Delta_M={s=sigma+it : sigma>1-c_M/log(3+|t|)}

all nonprincipal L_O(s,chi) and (s-1)L_O(s,1) are holomorphic and nonzero.
Take c_M smaller if necessary so Delta_M lies in Re(s)>3/4. Any exceptional
real zero is excluded by this fixed-M choice. These functions have analytic
logarithms on Delta_M, normalized from Re(s)>1, with logarithms
O_M(log(3+|t|)) in a slightly smaller such region intersected with
the fixed strip Re(s)<=2 (the only strip used below). This last, more than
sufficient, bound is a standard consequence of fixed-conductor zero-free
and growth estimates. No GRH, Artin holomorphy conjecture, or modulus-uniform
zero-free assertion is used: all the L-functions here are abelian Hecke
L-functions over Q(i).

It follows from (2.4) that, on Delta_M slit to the left of 1,

    D(s)=exp(V log(1/(s-1))) H(s),                               (2.5)

where H is E-valued, holomorphic on Delta_M, and, in that fixed strip, of at most polynomial growth
in |Im(s)|. The same assertions hold for the finite Euler factors and the
normally convergent error exponential used above. Singular behavior at 1 is
therefore completely captured by the **single finite matrix** V acting by
left multiplication on E.

## 3. The leading eigenvalue has no logarithmic Jordan factor

For any state W, multiplication by e_W sends each basis vector to a basis
vector. Its matrix is nonnegative with every column summing to one. Thus
2V, acting on E, is a column-stochastic matrix and

    ||(2V)^k||_(l1 -> l1)<=1 for every k>=0.

Consequently every eigenvalue beta of V satisfies |beta|<=1/2. The eigenvalue
1/2 is semisimple: a nontrivial Jordan block there would make the powers of
2V unbounded. It is also the only eigenvalue with Re(beta)=1/2. All other
eigenvalues have a strictly smaller real part, with a positive gap depending
only on M. This argument works in the full algebra, including nonunit states;
no unjustified semisimplicity of a finite monoid algebra is assumed.

Jordan decomposition of (2.5), followed by l_B, yields a finite expansion
near 1 of the form

    D_B(s):=sum_(m>=1) l_B(a(m))m^(-s)
      = sum_beta sum_(k=0)^(d_beta-1)
          (s-1)^(-beta) (log(1/(s-1)))^k H_(beta,k)(s),           (3.1)

with H_(beta,k) holomorphic near 1, |beta|<=1/2, and d_(1/2)=1.
The holomorphic factors come from the spectral projectors and powers of the
nilpotent parts applied to H(s). They satisfy the needed polynomial growth
on Delta_M. Lower eigenvalues may have Jordan factors: these are precisely
why powers of log log X must be allowed.

## 4. The required finite-singularity Selberg--Delange step

Here is the analytic transfer in sufficient detail to specify both its
hypotheses and its remainder. Suppose a scalar Dirichlet series with bounded
coefficients has a continuation as in (3.1) in a slit Delta_M, of polynomial
growth, with finitely many exponents of real part at most rho. Suppose its
holomorphic factors have Taylor expansions at 1. For every fixed integer
J>=1 its summatory function has the expansion

    x sum_beta sum_k sum_(j=0)^(J-1)
       h_(beta,k,j) [partial_beta^k
                    { (log x)^(beta-j-1)/Gamma(beta-j) }]
       + O(x (log x)^(rho-J-1) (log log x)^d),                  (4.1)

where h_(beta,k,j) is the coefficient of (s-1)^j in
H_(beta,k)(s)/s, and d can be taken to be the largest k. The derivative acts
only on the displayed Gamma expression, not on h. The formula is valid also
when beta-j is a nonpositive integer, because 1/Gamma is entire. In that case
one must retain its derivatives rather than informally discard log terms.
For the present application rho=1/2.

**Proof of this transfer.** Bounded coefficients permit a particularly simple
unsmoothing. Put L=log x and epsilon=L^(-B), with B fixed sufficiently large
relative to J. Choose phi_epsilon by rescaling one fixed smooth transition, equal to 1
on [0,1], zero on [1+epsilon,infinity), and between 0 and 1. Thus its
r-th derivatives are O_r(epsilon^(-r)). Replacing the sharp sum by
sum a(n)phi_epsilon(n/x) changes it by O(x epsilon+1). Its Mellin transform is

    phi_hat(s)=1/s+O(epsilon) near s=1,
    phi_hat(s) <<_q epsilon^(-q)(1+|Im(s)|)^(-q-1)

on the relevant fixed-width vertical strip, for every fixed q. The first
bound holds with fixed-order derivatives as well; it follows by integrating
over [1,1+epsilon]. The second follows by integration by parts.

Apply Mellin inversion on Re(s)=1+1/L, truncate at T=exp(sqrt L), and move
the contour inside Delta_M to a Hankel contour around the slit ending at 1.
Choose q larger than the polynomial growth exponent plus two. The Mellin
bounds, and x^sigma<=x exp(-c L/log(3+|t|)) on the shifted contour away from
1, make all the non-Hankel and tail contributions
O(x L^(Bq+O(1)) exp(-c' sqrt L)). Here c'>0 is fixed; low-height portions
outside a fixed small disk about 1 are even exponentially smaller in L.
Thus these errors are smaller than x times any fixed negative power of L.

Write w=s-1. On the local Hankel contour, take the small circle |w|=1/L and
rays along the two sides of the negative real axis up to a fixed small
radius. Replace H_(beta,k)(s)/s by its Taylor polynomial through degree J-1.
The remainder contributes

    O(x L^(Re(beta)-J-1) (log L)^k),

as is seen directly from the circle and the integral of
exp(-Lu)u^(J-Re(beta))(|log u|+pi)^k along the rays. Extending each monomial's
Hankel rays to infinity costs an exponentially small error. The Hankel
identity and differentiation in beta give exactly

    (1/(2 pi i)) integral exp(w L) w^(j-beta)(log(1/w))^k dw
      = partial_beta^k {L^(beta-j-1)/Gamma(beta-j)}.

Finally phi_hat-1/s has local analytic coefficients O(epsilon) and contributes
O(x epsilon L^(rho-1)(log L)^d). Taking, in our application, B>=J+2 absorbs
this and the sharp/smooth error in (4.1). This proves (4.1) without any
positivity hypothesis or a scalar multiplicativity assumption. QED.

### Consequence for actual F_B

Apply (4.1) with J=2 and rho=1/2. There is a real smooth function h=h_(M,B)
which is a finite linear combination of

    L^(beta-j-1) (log L)^k,     j=0,1,

such that, for L=log X,

    F_B(X)=X h(L)+O_M(X L^(-5/2)(log L)^d).                     (4.2)

Complex conjugate terms can be paired, so h is real for real L. There is an
eta_M>0 for which, writing a=kappa lambda,

    h(L) = a L^(-1/2)+O_M(L^(-1/2-eta_M)(log L)^d),
    h'(L)=-a/2 L^(-3/2)+O_M(L^(-3/2-eta_M)(log L)^d).           (4.3)

For example choose eta_M as the minimum of 1 and the gap from 1/2 to the
real parts of the other eigenvalues; use eta_M=1 if there are no others.
The coefficient a is identified by the audited first-order asymptotic (0.1).
Semisimplicity at 1/2 is what excludes a top-order log L factor. All other
terms and their derivatives obey (4.3).

Equation (4.2) is an expansion for actual accepted norms, NOT an estimate of
the saturation error by its remainder. Its lower-log-power terms can be much
larger than X/(log X)^(3/2).

## 5. Passing to actual distances at both scales

Put X=4R^2, L=log X, and c=pi delta/4. The audited endpoint construction says
that every permitted difference vector of length at most 2R-sqrt(2)M has both
endpoints in P_R. Hence

    0<=F_B(4R^2)-D(P_R)<=4 sqrt(2)MR+1,                         (5.1)

for R>=M/sqrt(2). In particular, (0.1) and (4.2) give

    n_R=cX+O_M(sqrt X),
    D(P_R)=X h(L)+O_M(X L^(-5/2)(log L)^d+sqrt X).

Since h(L)~a/sqrt L and a>0, elementary division and squaring yield

    K(P_R)^2 = G(L)+o(1),           G(L)=c^2/h(L)^2.              (5.2)

More explicitly, the error is
O_M(L^(-1)(log L)^d+L^(3/2)/sqrt X), which tends to zero. Thus the geometric
boundary loss, as well as the analytic remainder, is negligible on the
**additive squared-potential scale**.

By (4.3),

    G'(L)=-2c^2 h'(L)/h(L)^3 -> c^2/a^2.                       (5.3)

Apply (5.2) separately at R and tR. Their arguments of G differ by
log(t^(-2)), so integrating (5.3) proves (0.2). The same proof works for any
r_R/R->t in (0,1), because both analytic errors are o(1) and the shift of L
then tends to log(t^(-2)).

This is the required cancellation: differentiability of the finite smooth
expansion controls the increments. An arbitrary o(1) relative error in F_B,
or even a sublinear error in K^2, would not justify this step.

## 6. Exact uniformity and a restricted finite-endpoint consequence

Let gamma=(pi/(4 kappa))^2.

### Quantifiers

For every epsilon>0 and every fixed integer M there exists R_0(M,epsilon)
such that, for **all** nonempty A subset O/(M) and all R>=R_0,

    |K(P_R)^2-K(P_(R/2))^2
       -gamma (delta/lambda)^2 log 4| < epsilon.                (6.1)

There are only finitely many A at a fixed M, so the estimates can be made
uniform over A, either directly from the common finite algebra or by taking
a maximum of thresholds. Consequently, for every fixed M,

    lim_(R->infinity) max_(nonempty A) [K(P_R)^2-K(P_(R/2))^2]
       = gamma log 4.

Equality in the limiting bound is attained by a singleton A: then
B={0}, F_B(X) counts norms up to X/M^2, and lambda=delta=1/M^2.
The same conclusions are uniform over any fixed finite range of moduli.
There is **no assertion of useful control of R_0 as M grows**, nor an
interchange of the large-R limit with the supremum over all M.

### Actual nearly-half-size child, with eventual loss 1

Let h_0=M/sqrt(2), the covering radius of MO. Tiling separately for each
residue coset gives, for every u>=0,

    delta pi (u-h_0)_+^2 <= n_u <= delta pi (u+h_0)^2.            (6.2)

For sufficiently large R choose the explicit actual subset

    r_R=(R-h_0)/sqrt(2)-h_0,       Q_R=P_(r_R) subset P_R.

Then r_R+h_0=(R-h_0)/sqrt(2), so (6.2) proves

    2<=|Q_R|<=n_R/2,          |Q_R|/n_R -> 1/2.

The lower bound 2 holds for all sufficiently large R. Section 5 gives

    K(P_R)^2-K(Q_R)^2
       -> gamma (delta/lambda)^2 log 2 <= gamma log 2
       =0.73208965983... <1.                                   (6.3)

Therefore, for every fixed M and all its masks, once R exceeds a threshold
depending on M,

    Q_R subset P_R,   2<=|Q_R|<=|P_R|/2,
    K(Q_R)^2 >= K(P_R)^2-1.                                    (6.4)

This is a genuine finite-endpoint result for large periodic disks. The strict
inequality gamma log 2<1 does not rely on the decimal: the Euler product gives
kappa>=1/sqrt(2), and pi^2 log 2/8<1. One may also take floor(r_R), changing
r_R by O(1) without changing (6.3) or violating the cardinality bound.
It does NOT prove (6.4) at arbitrary original heights, or bound the potential
at the mask-dependent stopping scale of an iteration.

### Modulus-uniform centered contraction is actually false

For integers t->infinity let

    E_t={z in O : t/2<|z|<=t} union {0,1},
    M_t=5t,       A_t=E_t mod M_t.

At height t the corresponding periodic disk is exactly E_t: no nontrivial
translate by M_t O can enter the disk. Its centered child at height t/2 is
exactly {0,1}, with K^2=4. On the other hand,

    |E_t|=(3pi/4)t^2+O(t),
    D(E_t)<=S(4t^2)~4 kappa t^2/sqrt(log(4t^2)),

where S counts all positive sums of two squares. It follows for the **actual**
parent potential that

    K(E_t)^2 >= ((3pi/(16 kappa))^2+o(1)) log(4t^2) -> infinity.

Thus its actual centered parent--child defect tends to infinity, with
M_t/t=5. This does not contradict the fixed-mask theorem: the mask changes
with t. It also does not refute contraction by an arbitrary subset Q.
The displayed use of S is only a rigorous upper bound on actual D to prove
this counterexample; no equality with a capacity is assumed.

More generally, any finite Gaussian set inside a radius-t disk is encoded by
its residues modulo an integer M>4t. At that height the periodic disk is the
set itself and F_(A-A)(4t^2)=D of the set: two vectors of length at most 2t
cannot differ by a nonzero element of MO. Thus M comparable with the original
height already encompasses arbitrary finite **Gaussian** endpoint sets.
No arbitrary-planar-set reduction is being asserted.

## 7. The saved mod-13 example: an exact stronger deficit theorem

Take M=13, A={0,2+6i}. The audit gives

    delta=2/169,    lambda=14/169,
    C_B(X)=#{m<=X : m is a norm, and (m=1 mod 13 or 169|m)}.

In G=(O/(13))^*/U, the scalar norm map to F_13^* is surjective and its kernel
H has order 3. Conjugation acts by inversion on H. The map
c -> c/conjugate(c) takes values in H and is surjective, since on H it is
squaring. Thus J=Fix(conjugation) has order 12, J intersect H={1}, and the
scalar norm maps J bijectively to F_13^*. The orbit of 2+6i is a nonidentity
element of H.

Call a rational split prime q!=13 **inactive** if the Gaussian prime class
above it lies in J; this is independent of which prime above q is chosen.
Let Q_0 be the inactive prime set. If q=a^2+b^2, an equivalent explicit test is

    q in Q_0 iff a b (a-b)(a+b)=0 mod 13.                        (7.1)

Indeed a+bi is a unit multiple of a-bi modulo 13 exactly in those four
axis/diagonal cases. The total rational prime density of Q_0 is
|J|/(2|G|)=1/6, by the fixed ray-prime theorem, or directly by (2.3).

Every norm divisible by 169 has a representation divisible by 13, so is
actually accepted in the zero residue. For m=1 mod 13, all classes in W(m)
lie in H and W(m) is nonempty and conjugation-invariant. It fails to contain
the class of 2+6i if and only if W(m)={1}: the other two elements of H are
interchanged by conjugation. Formula (1.1) shows that an active split prime
factor gives a state of size at least two, at every positive exponent. In a
group, a product of nonempty subsets has cardinality at least that of either
factor. Conversely, if all split prime factors are inactive, every prime-power
state is a singleton in J (also at 2 and at the even inert prime powers), and
the condition m=1 mod 13 forces their product to be the identity. Therefore

    C_B(X)-F_B(X)
      =#{m<=X : m is a norm, m=1 mod 13,
                    every split prime factor of m belongs to Q_0}.            (7.2)

This is an exact identity at every height, not a sieve upper bound.

Define the positive Euler product, initially for Re(s)>1,

    Z_0(s)=(1-2^(-s))^(-1)
           product_(p=3 mod 4) (1-p^(-2s))^(-1)
           product_(q in Q_0) (1-q^(-s))^(-1).

It counts norms avoiding 13 and all active split primes. The same Hecke
factorization shows

    Z_0(s)=(s-1)^(-1/6) H_0(s),       H_0(1)>0.                 (7.3)

Positivity and nonvanishing follow either from the logarithmic Euler-product
factorization or its convergent positive normalized product.
To impose m=1 mod 13, average its twelve twists by Dirichlet characters
chi modulo 13. The logarithmic singular exponent of a twist is

    (1/(2|G|)) sum_(c in J) chi(N(c))
       = 1/6 if chi is principal, and 0 otherwise,

because N:J->F_13^* is a bijection. Nonprincipal twists are holomorphic at 1
and have no Hankel contribution; the transfer in Section 4 makes their sums
smaller than X times any fixed negative power of log X. It follows that

    C_B(X)-F_B(X)
       = eta_13 X/(log X)^(5/6) (1+O(1/log X)),
    eta_13=H_0(1)/(12 Gamma(1/6))>0.                             (7.4)

In particular, with c=pi delta/4 and a=kappa lambda, the actual disk potential
satisfies

    K(P_R)^2-(n_R/C_B(4R^2))^2
       ~ (2 c^2 eta_13/a^3) (log(4R^2))^(2/3).                 (7.5)

To see this, use C_B~aX/sqrt(log X), (7.4), D(P_R)=F_B(X)+O(sqrt X),
and expand the difference of the inverse squares; the boundary error is
negligible compared with (7.4). This strengthens, rather than contradicts,
the earlier sqrt(log X) lower bound. Yet the actual centered-half defect is

    K(P_R)^2-K(P_(R/2))^2 -> C_4/49=0.02988121060... .           (7.6)

The growing lower-power potential terms have vanishing fixed-log-shift
increments, with the rigorous remainder supplied by Sections 4--5.

## 8. Verification, references, and remaining gap

`verify_periodic_norm_two_scale.py` uses standard-library integer arithmetic
for all assertions. Its output is saved in
`periodic_norm_two_scale_verification.txt`. It checks:

- complete Euler-state reconstruction for every m<=2000 at nine moduli,
  including nonunit residues: 18,000 states and 97,299 coprime products;
- |G|=36, |H|=3, |J|=12 and the norm bijection J->F_13^*;
- the 36-state mod-13 unit submonoid: 2V is column stochastic and
  V(V-1/2)(V-1/6)^2=0, but V(V-1/2)(V-1/6) is nonzero. Lower Jordan blocks
  really occur, so retaining possible log log terms is important;
- (7.2) at every integer through 1,000,000, independently using Gaussian
  vector enumeration and prime-factor classification. At X=10^6 it recovers
  S(X)=216341, C_B(X)=18153, F_B(X)=15059, missing=3094;
- direct pairwise actual D at parent and child scales for nine periodic disks,
  the covering-radius endpoint sandwich, and explicit near-half-size subsets;
- exact finite instances of the varying-modulus annulus encoding, including
  actual D at both scales and F_(A-A)(4t^2)=D(E_t).

Displayed decimals are for orientation only. Finite checks do not establish
an asymptotic; the analytic proof above does.

Beyond the saved audited theorem, the analytic input is standard fixed-order
Hecke L-function continuation, nonvanishing at 1, and a fixed-conductor
zero-free region with growth estimates, stated explicitly in Section 2.
For comparison with the scalar argument, the local source
`/corpus/src/1904.12845/1904.12845.tex` (Daniel Loughran and Lilian Matthiesen,
*Frobenian multiplicative functions and rational points in fibrations*),
lines 534--605, proves the scalar Euler-product factorization using the same
character/zero-free method and cites Tenenbaum, Theorem II.5.3, for
Selberg--Delange. This note does not treat its scalar theorem as directly
applicable to the nonmultiplicative acceptance indicator: Sections 1--4
supply the algebra-valued reduction, the Jordan analysis, and the necessary
unsmoothed transfer with remainder.

**Remaining gap:** there is still no height-free actual-support estimate for
arbitrary finite endpoint selections, nor a bounded unrestricted contraction
defect. The eventual periodic result (6.4) cannot be applied at arbitrary
M comparable with R, or iterated past a mask-dependent stopping scale with a
uniform bound on its residual potential. No Lean files were edited and no
solution of D>=c n/sqrt(log n) for arbitrary planar point sets is claimed.
