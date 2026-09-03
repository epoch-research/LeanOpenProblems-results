# Higher differential elimination and adjoint constructions

External exact arithmetic and mathematical analysis, NOT Lean declarations
and NOT a proof or disproof of Erdős 68. Spec.lean is unchanged and still
contains its original sorry. No complete informal solution has been obtained.

## Common differential operators

Put theta=z*d/dz and E_j(z)=sum_(n>=0) z^n/(n!)^j. Then

    (theta^j-z) E_j = 0.

Exact common left multiples were constructed for j=1,...,J, J=1,...,5,
with orders M=J(J+1)/2. Remainders of powers of theta modulo theta^j-z
were computed by rational-function linear algebra. Clearing denominators
gave integer polynomial coefficients. The independent audit instead uses
right division and theta^k*z=z*(theta+1)^k to verify every annihilation.

For J=2 the common operator is particularly simple:

    L_theta = (theta-z-2)*(theta^2-z)
            = theta^3-(z+2)*theta^2-z*theta+z^2+z.

After converting to ordinary derivatives and removing a common factor z,

    L = z^2 D^3 + z(1-z) D^2 -(1+2z)D +(1+z)
      = (zD-z-1)*(zD^2+D-1).

For F(z)=sum_(n>=2) z^n/(n!-1), a direct rational identity gives

    L F = -(16/5) z^2 + sum_(n>=3) c_n z^n,

where

    c_n = (n-1)*(n^2+n-1)
          / [((n-1)!-1)*(n!-1)*((n+1)!-1)] > 0.

Indeed the coefficient is

    (n-1)*(n+1)^2/((n+1)!-1)
    -(n^2+n-1)/(n!-1)+1/((n-1)!-1).

This is genuine cancellation of the first two factorial-power columns.
It does not make F'(1) or F''(1) rational from rationality of F(1).
The displayed identity is mathematical analysis and symbolic rational
arithmetic here, not a new Lean-verified theorem.

## Polynomial adjoint test

For each common ordinary differential operator L=sum a_l(z)D^l, remove
the common polynomial factor of its coefficients. Write

    beta_J(z)=sum_(j=1)^J [E_j(z)-1-z],
    L beta_J = -J L(1+z) = f_J(z).

For N in {0,2,4,8,12,16,24,32}, let D=N+M-1 and solve for a polynomial Q
of degree at most D such that

    [z^n] L*Q = 0   for n<N,
    Q^(l)(1)=0     for l<M-1.

Here L*Q=sum_l (-1)^l D^l(a_l Q). All 40 systems had a one-dimensional
kernel and nonzero

    A=(-1)^(M-1)*a_M(1)*Q^(M-1)(1).

Green's formula supplies a rational boundary

    B=integral_0^1 Q*f_J + boundary_at_zero(beta_J,Q).

The latter boundary uses only finitely many rational Taylor coefficients.
The audit checks Green's formula independently on a finite Taylor polynomial.
No general small-error or convergence assertion is made from these equations.

For every K=1,...,max(8,2D), form the corrected rational candidate

    R_K=B/A+sum_(n=2)^K 1/[(n!)^J*(n!-1)].

The omitted positive tail against the FULL target is retained when checking
its reduced integer form b*alpha-a. All 1,476 cases were exactly classified:

* 1,474 errors exceed one;
* two errors lie in (0,1), giving (a,b)=(1,1) and (67,54).

Both small cases have J=1. They supply no infinite family. In particular,
merely forcing a high-order zero of L*Q at zero does not establish a useful
approximation theorem for the higher-order system.

Artifacts:

* /tmp/differential_adjoint_forms.py, .json, .log
* /tmp/differential_adjoint_forms_audit.py, .log

## A logarithmic adjoint test for J=2

The polynomial restriction misses adjoint solutions with logarithms. For
the order-three operator above,

    L*=(zD^2+D-1)*(-zD-z-2).

Three adjoint solutions can be written in terms of the following rational
coefficient series (q_K contains one log z):

    q_C=z^(-2)*exp(-z),
    q_I=sum i_n*z^n,
    q_K=q_I*log z + sum r_n*z^n,

where, with i_(-1)=r_(-1)=0 and H_n=sum_(k=1)^n 1/k,

    i_n=-(1/(n!)^2+i_(n-1))/(n+2),
    r_n=(2*H_n/(n!)^2-i_n-r_(n-1))/(n+2).

The exact experiment truncates q_C through degree NC and the other two
through degree N. It takes their rational linear combination Q with
Q(1)=Q'(1)=0. The coefficients are obtained by a cross product, not by
floating-point solving. The retained coefficient is A=Q''(1).

Since beta_2 starts with (3/4)z^2, the boundary at zero is 3C, where C is
the coefficient of q_C. Also L beta_2=-2z^2. Thus the exact rational
boundary is

    B=3C-2*integral_0^1 z^2*Q(z) dz.

All logarithmic integrals are evaluated rationally by
integral z^m log(z)=-1/(m+1)^2. The pole in q_C is canceled by z^2.

Parameters N=0,1,2,3,4,6,8,12,16,24,32 and distinct NC in {N,2N,3N}
give 31 systems. For each, K runs through 1,...,max(8,2*max(N,NC)), with
the same full-target correction, now at J=2. All 1,322 cases were classified:

* 1,287 errors exceed one;
* 35 errors are less than minus one;
* none lie in [-1,1].

The unscaled candidates in the later cases are close to beta_2(1), but
that does not compensate for their reduced denominator sizes. These finite
results do not rule out other choices or prove an asymptotic obstruction.

The independent audit reconstructs i_n,r_n by convolution formulas obtained
from integrating the two Bessel solutions, rather than by their recurrence.
It differentiates Laurent-logarithmic polynomials directly, checks both
endpoint conditions, both boundary coefficients, the limiting zero boundary,
and Green's formula on a finite Taylor polynomial. It checks every reduced
candidate and every full-target interval classification.

Artifacts:

* /tmp/logarithmic_adjoint_forms.py, .json, .log
* /tmp/logarithmic_adjoint_forms_audit.py, .log

## Certification and remaining gap

Both constructions use the exact factorial-grid enclosure with N=2000:

    W=N!, L=sum_(n=2)^N floor(W/(n!-1)),
    L/W < alpha < (L+N+2)/W.

Both independent audits reconstruct all retained intervals and recheck their
classifications using a second grid at N=2017. All audits passed. Logs of
sizes are diagnostics only. No floating-point comparison is a premise.
Neither experiment has been imported as a Lean proof.

No family of nonzero integer forms tending to zero has been obtained. The
exact denominator recurrence still has no proven integer-height descent.
All computations have completed; nothing is pending. Spec.lean is unchanged,
and no new submission check has been made.
