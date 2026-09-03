# Factorial-gap integrals: exact normalization and an auxiliary-free certificate

## Outcome and scope

No irrationality proof for S = sum_{n>=2} 1/(n!-1) was found. In particular,
there is no claimed infinite sequence of nonzero integer linear forms tending
to zero. `Submission/Spec.lean` was not edited or imported.

The new calculations in this investigation concern two different meanings of
“factorial-gap powers.” They give sharp, explicit local normalization costs,
not merely small unnormalized integrals. A separate factorial-difference
construction gives **pure S integer linear forms from the outset**, together
with a congruence-based nonvanishing test. Its missing ingredient is stated in
Section 5. The construction does not solve the previously identified
short-image problem by introducing extra coefficient variables.

Write

    F_n = n!,   a_n = F_n - 1,   d_n = F_{n+1} - F_n = n F_n.

All unit-interval integrals below are ordinary convergent real integrals. In particular,
Tonelli gives S = integral_0^1 sum_{n>=2} x^(a_n-1) dx. Convergence follows,
for example, from 1/(n!-1) <= 2/n!.

## 1. Putting the gap inside x: exact primitive arithmetic, but weak decay

For n>=2 and m>=0 define

    I(n,m) = integral_0^1 x^(a_n-1) (1-x^d_n)^m dx.

Repeated integration by parts, or y=x^d_n, gives the exact formula

    I(n,m) = m! d_n^m / product_{j=0}^m (a_n+j d_n)
           = (1/a_n) product_{j=1}^m (1+a_n/(j d_n))^(-1).             (1)

One direct integration-by-parts proof is

    (a_n+m d_n) I(n,m) = m d_n I(n,m-1),   I(n,0)=1/a_n.

### Arithmetic normalization

Let P(n,m)=product_{j=0}^m(a_n+j d_n). The exact factorial shift matters:

    gcd(a_n,d_n)=1.

Indeed a_n=n!-1 is coprime to n!, and n divides n!. Consequently every factor
of P(n,m) is coprime to d_n. Set

    g(n,m)=gcd(P(n,m),m!).

The **reduced** numerator and denominator of I(n,m) are therefore exactly

    numerator   = (m!/g(n,m)) d_n^m,
    denominator = P(n,m)/g(n,m).                                    (2)

In particular the reduced numerator is at least d_n^m. No power of the
factorial gap cancels against the denominator.

There is an especially clean range: if m<=n, then

* every a_n+j d_n is congruent to -1 modulo n!, so g(n,m)=1;
* these m+1 numbers are pairwise coprime.

For the second assertion, a common divisor of the i-th and j-th numbers
divides (j-i)d_n, hence divides j-i since it is coprime to d_n. But j-i<=n
and all primes <=n divide n!, whereas none divides a_n+i d_n.

Example: n=3,m=2 gives

    integral_0^1 x^4(1-x^18)^2 dx
      = 1/5 - 2/23 + 1/41 = 648/4715.

The denominator 41 is genuinely an additional node, not another factorial
minus one.

### Analytic size

Put alpha=a_n/d_n<1/n, and H_m=sum_{j=1}^m 1/j. From log(1+u)<=u,

    I(n,m) >= (1/a_n) exp(-alpha H_m)
            >= (1/a_n) exp(-H_m/n).                                 (3)

For m<=n this is at least exp(-(1+log n)/n)/a_n. Thus this natural range of
gap powers does not even substantially reduce the original summand.
To obtain I(n,m)<1/(a_n F_n^K), it is necessary that

    H_m > n K log F_n,   hence m > F_n^(nK)/e.                        (4)

The statement uses only the lower bound, not an asymptotic approximation.

### Formal auxiliary-node obstruction

For 2<=j<=m<=n,

    a_{n+1} < a_n+j d_n < a_{n+2}.

These nodes are not factorial-minus-one nodes, and their open intervals are
disjoint for different n. Hence in sums of kernels
x^(a_n-1) P_n(x^d_n), with deg P_n<=n, the monomials of degree j>=2 cannot
cancel against another row. If the integrand is required to collapse formally
to A sum x^(a_n-1) plus a finite polynomial, then eventually only the constant
and linear powers in x^d_n can remain. For kernels vanishing at x=1 these are
w_n(1-x^d_n); formal collapse then requires w_n-w_{n-1}=A eventually.

This is a statement about formal monomial cancellation, **not** an assertion
of linear independence of numerical sums. It does not exclude deeper global
arithmetic cancellation in unrestricted constructions.

## 2. Putting the gap on (1-x): rapid decay and its exact cost

Now use the very different integral

    B_n = integral_0^1 x^(a_n-1) (1-x)^d_n dx.

Let a=a_n and b=a_{n+1}=a+d_n. The beta evaluation gives

    B_n = 1/D_n,
    D_n = a binom(b,a) = b binom(b-1,a-1).                            (5)

So these integrals really are extremely small. But their primitive
arithmetic is already completely visible in (5).

Consecutive a and b are coprime. Thus ab divides D_n. The least positive
integer C for which

    C B_n belongs to Z + (1/a)Z + (1/b)Z

is **exactly**

    C_n = D_n/(ab),   C_n B_n=1/(ab).                               (6)

Proof: the group on the right is (1/(ab))Z. The membership condition is
D_n | Cab, which, since ab|D_n, is equivalent to D_n/(ab) | C.

There are explicit smooth Bezout coefficients, not an unspecified gcd:

    u_n=(n-1)!,   v_n=(n+1)(n-1)!+1,
    u_n b - v_n a = 1,

and hence

    C_n B_n = u_n/a_n - v_n/a_{n+1}.                                (7)

For example, n=3 gives

    B_3=integral_0^1 x^4(1-x)^18 dx=1/168245,
    C_3=1463,
    C_3 B_3=1/115=2/5-9/23.

Equations (6)-(7) answer the local integration-by-parts normalization
question exactly: integer coefficients of the two factorial endpoint
reciprocals are possible, but the spectacular beta decay is lost. The
logarithm of D_n is of order n! log n, whereas after this minimal endpoint
normalization the value is only 1/(a_n a_{n+1}). Further normalization to an
ordinary integer multiplies by ab and gives 1.

This does not prove that all *global* combinations of many beta integrals
fail. It specifies the cost of local elimination of their interior poles.
Any successful global construction must beat that local cost through a
proved arithmetic cancellation, not simply through the beta estimate.

## 3. Gamma contours: where the extra arithmetic enters

For a finite contour in Re(s)>1, consider

    K_h(s)=pi cot(pi s) h(s)/(Gamma(s+1)-1),

where h is holomorphic on and inside the contour. Avoid zeros and integer
poles on the contour. At an integer n>=2 the residue is

    h(n)/(n!-1).

At a simple noninteger zero rho of Gamma(s+1)-1 it is

    pi cot(pi rho) h(rho)/Gamma'(rho+1).                             (8)

Thus the residue theorem gives the desired finite integer-node sum **plus**
(8) for every such zero enclosed. Multiple zeros introduce derivatives as
well; they do not give automatic integer residues. One can keep a contour
in a thin region excluding these zeros, but then the result is just an exact
representation of the original sum, without a new arithmetic normalization.

If one changes h by (Gamma(s+1)-1)G(s), with G regular at rho, the residue
(8) is unchanged. In particular a numerator congruent to a nonzero constant
A modulo Gamma(s+1)-1 retains the corresponding A-weighted root residues.
Cancelling the root poles by a factor Gamma(s+1)-1 also cancels the target
factorial-minus-one denominators.

Multiplying instead by Gamma'(s+1) does not fix this. At integer nodes the
residues become

    n! (H_n-gamma)/(n!-1),

and at a simple noninteger root they become pi cot(pi rho), still not
ordinary integers. Dropping the cotangent gives the argument principle, but
then the integer nodes no longer contribute S.

No arithmetic identity controlling the aggregate root residues, and no
alternative deformation with a useful integer normalization, was found.
This is the exact missing arithmetic step in this contour route; contour
decay by itself is insufficient.

## 4. An auxiliary-free polynomial-difference integral

This construction is deliberately variable-complexity; it is not a claim
that S has a fixed rational telescoper.

Choose A in Z, K>=1, and an integer-valued polynomial

    p(n)=sum_{j=0}^d c_j binom(n-1,j),   c_j in Z.

Set

    h(n)=n^K p(n-1)-p(n),
    R_n=A/(n!-1)+h(n)/(n!)^K.

The factorial shift gives, term by term,

    h(n)/(n!)^K = p(n-1)/((n-1)!)^K - p(n)/(n!)^K.

All these series converge absolutely. Therefore

    J(A,p,K):=sum_{n>=2} R_n = A S+p(1)=A S+c_0.                    (9)

Both coefficients on the right are integers. There is no prefix lcm, no
hyper-Bessel value, and no unidentified auxiliary constant. In integral form,

    J(A,p,K)=sum_{n>=2} integral_0^1
      [ A x^(n!-2)
        + h(n)/(K-1)! x^(n!-1) (-log x)^(K-1) ] dx.                  (10)

Absolute integrability justifies the interchange: the absolute integrals
are bounded by |A|/(n!-1)+|h(n)|/(n!)^K.

### A congruence-based nonzero estimate

Define the integer

    Q_n=A (n!)^K+(n!-1)h(n).

Then

    R_n=Q_n/[(n!-1)(n!)^K],   Q_n == A (mod n!-1).                   (11)

Suppose A>0 and Q_n>=0 for every n>=2. Let r_n be the least nonnegative
residue of A modulo n!-1. Integrality gives Q_n>=r_n, not just Q_n>=0.
Consequently

    J(A,p,K) >= sum_{n>=2} r_n/[(n!-1)(n!)^K].                       (12)

For any n with n!-1>A, r_n=A, so in particular

    J(A,p,K) >= A/[(n!-1)(n!)^K] > 0.                               (13)

This uses the exact shift n!-1 and supplies nonvanishing after integer
normalization. Positivity cannot be inferred merely from small numerical
values; it must be proved for the Q_n.

### A fully explicit finite upper certificate

Write p in the ordinary power basis, with degree at most d, and let C_p be
the sum of the absolute values of its rational coefficients. Put

    D=d+K,   C=2A+2C_p.

For n>=2,

    |R_n| <= C n^D/n!.

If M>=max(2,2D), the ratio of successive n^D/n! is at most 2/(M+2) for
n>=M+1. Hence

    sum_{n>M}|R_n| <= C (M+2)/M * (M+1)^D/(M+1)!.

Thus the rational quantity

    U(A,p,K,M)=sum_{n=2}^M R_n
              + C (M+2)/M * (M+1)^D/(M+1)!                         (14)

is a rigorous upper bound for J. With (11)-(13), proving Q_n>=0 and making
(14) small would give the required nonzero integer linear forms.

### A nontrivial check, not an irrationality proof

Take A=4,K=3 and

    p(n)=-5-3 binom(n-1,1)-33 binom(n-1,2)
           -299 binom(n-1,3)+7995 binom(n-1,4).

Then p(1)=-5, so J=4S-5 is already primitive. In the power basis,

    24p(n)=7995n^4-81146n^3+286605n^2-411790n+198216.

For n=2,3,4,5 the values of h are -32,-172,-2404,-58084. They give
nonnegative residuals; specifically R_2=0 and R_3=1/270.
For u>=0 one has the exact polynomial identity

    24h(u+6)=7995u^7+222664u^6+2549697u^5+15426137u^4
              +52658546u^3+99830511u^2+94909306u+33252216.

Every coefficient is positive, proving h(n)>0, hence R_n>0, for every n>=6.
In (14), D=7,C=82154,M=40 gives by exact rational arithmetic

    0 < 4S-5 < 1/71.                                                (15)

This example checks normalization, convergence, and a global sign proof.
It is not a new lower bound of independent significance, and one such
small form cannot prove irrationality.

## 5. Precise unresolved construction problem

Find an explicit sequence (A_N,p_N,K_N,M_N), with A_N a positive integer,
p_N integer-valued as above, K_N>=1, M_N>=max(2,2(deg(p_N)+K_N)), such that

    Q_{N,n}>=0 for every n>=2,
    U(A_N,p_N,K_N,M_N) -> 0.                                        (16)

A finite positivity certificate could consist of exact checks up to a
cutoff and a nonnegative-coefficient expansion (as in the example) or
another proved tail inequality. Formula (13) would guarantee nonzero forms.
If S=a/b were rational with b>0, then b J_N would be positive integers tending
to zero, a contradiction. So (16), if proved, would finish the problem.

**No such sequence is established here.** In particular, c_1,...,c_d are
exact-zero directions for the value in (9); the integer image is only
(A,c_0). Making a coefficient vector short in that larger space proves
nothing about a nonzero small image. Also, a family found by fitting p to
already-known good rational approximations of S would be circular as an
irrationality proof. The missing result is a simultaneous, independently
proved sign-and-size construction, not another analytic-decay estimate.
The telescoping identity alone could be added to any convergent series and
is not evidence of irrationality. It is the congruence (11), together with
an as-yet-unproved useful sign-and-size family, that would exploit the exact
factorial-minus-one denominator. Factorial-scale rational Egyptian sums
therefore do not contradict any theorem asserted here.

The local results in Sections 1-2 do not supply (16), nor do they rule out
every possible global integral construction. They rule out treating
factorial-gap integration by parts as a free denominator-clearing mechanism.

## 6. Verification and formalization status

New files:

* `Submission/FactorialIntegralCertificates.lean`
* `Submission/FactorialIntegralAudit.lean`
* `Submission/integral_verify.py`
* this report.

The Lean file proves:

* factorial-difference identities for finite sums and convergent infinite sums;
* an explicit exponential summability criterion;
* summability for every finite integer Newton coefficient vector, using
  binom(n,j)<=2^n;
* `newton_integer_linear_form`, with summability discharged, not assumed;
* congruence (11), nonvanishing under the explicit factorial bound, and the
  positive integer-form criterion;
* the explicit endpoint Bezout and reciprocal identities (7);
* the scaled quartic's boundary values and its global shifted-coefficient
  positivity identity.

The beta integral evaluations, the minimal local multiplier theorem (6),
the contour residue calculation, and the complete numerical upper
certificate (15) are proved/explained above but are **not** claimed to have
been fully formalized in Lean. The Python script checks the beta formulas
and primitive fractions exactly, 80 finite telescope identities, the
Newton-to-power-basis polynomial conversion, the global positivity
polynomial identity, and the rational upper certificate. It uses no
floating-point evidence for irrationality.

Commands from `/workspace/leanproject`:

    lake env lean -o .lake/build/lib/lean/Submission/FactorialIntegralCertificates.olean \
      Submission/FactorialIntegralCertificates.lean
    lake env lean Submission/FactorialIntegralAudit.lean
    python3 Submission/integral_verify.py

No new theorem contains `sorry`, `admit`, or a new axiom. The audit prints
only `propext`, `Classical.choice`, and `Quot.sound`. `Spec.lean` remains
unchanged; its SHA-256 is

    c5c794ec0dcb35e079f78ce20043053fe0bf048aa47873395df7221ce5aea20d.

## 7. Relevant corpus check

`/corpus/src/math_0101187/math0101187.tex` was checked for the actual arithmetic
behind little-q-Legendre irrationality proofs. The essential features are
an exact multiplicative shift identity for its Stieltjes transform and a
cyclotomic common denominator with a proved size estimate. Neither feature
is inherited merely by replacing a geometric support by factorial support.

`/corpus/src/1010.0429/1010.0429.tex` was checked for gamma/orthogonal-polynomial
integral normalization. It supplies no identity eliminating the root
residues in (8) for Gamma(s+1)-1. No theorem from either source is used as an
unverified black box in the new calculations above.
