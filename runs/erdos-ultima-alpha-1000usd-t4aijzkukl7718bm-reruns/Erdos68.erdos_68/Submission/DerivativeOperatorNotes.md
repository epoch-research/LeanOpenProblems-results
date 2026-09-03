# Derivative-operator review (not a solution)

These are mathematical notes, not newly Lean-verified theorems. The review
has not produced a proof or disproof of Erdős 68.

Consider the direct entire generating function

    F(z) = sum_(n>=2) z^n/(n!-1),       F(1)=alpha.

Its factorial-power decomposition is

    F(z) = sum_(j>=1) [sum_(n>=0) z^n/(n!)^j - 1 - z].

For fixed j, the inner full series E_j(z) satisfies

    theta^j E_j = z E_j,       theta=z*d/dz.

These direct series use z^n, rather than the z^(j*n) rescaling in the
previous joint type-II Padé experiment. This review did not run or assert
results for a new Padé family in these variables.

## An exact first elimination

Writing d_n=n!-1, the coefficient identity for n>=2 is

    (n+1)/d_(n+1) - 1/d_n = -n/(d_n*d_(n+1)).

Thus

    F'(z)-F(z)
      = 2*z - sum_(n>=2) n*z^n/(d_n*d_(n+1)).

The first exponential column is eliminated, and the residual coefficients
have roughly squared-factorial decay. This is a valid functional identity,
not a claim that F'(1) is rational when F(1) is rational. It introduces the
new value F'(1); neither its integrality nor its rationality follows from the
hypothetical rationality of alpha.

## Later adjoint-integral review (not Lean-verified)

For any polynomial P, set Q=sum_j (-1)^j P^(j), so Q'+Q=P. With

    H(x)=sum_(n>=2) n*x^n/[(n!-1)*((n+1)!-1)],

integration by parts on [0,1] gives the exact identity

    Q(1)*alpha - integral_0^1 2*x*Q(x) dx
      = integral_0^1 P(x)*F(x) dx - integral_0^1 Q(x)*H(x) dx.

Thus only alpha occurs as an endpoint value, but there are TWO integrals
on the right. The second cannot be omitted when applying a Hermite/Niven
kernel to the first. Indeed the adjoint equation gives

    Q(x)=exp(1-x)*(Q(1)-integral_x^1 exp(t-1)*P(t) dt).

If P is small relative to Q(1), then Q(x)/Q(1) is close to exp(1-x),
not to zero. Consequently the H integral divided by Q(1) approaches the
strictly positive constant integral_0^1 exp(1-x)*H(x) dx. Merely making
the P integral small therefore does not make the proposed form small.

Subtracting a finite Taylor polynomial of H into the rational boundary
retains a further tail integral. Its coefficients have the rational
factorial-minus-one denominators displayed above. No compatible bound on
the REDUCED aggregate boundary denominator and the full remaining error
was obtained. This observation does not require clearing every auxiliary
coefficient separately, and is not an impossibility theorem for other
adjoint kernels or higher differential eliminations.

No new Lean declaration or complete mathematical proof was obtained in this
review. Renewed retrieval of the problem reference failed at DNS resolution;
a separate direct-IP connectivity attempt also timed out. No external
literature update was retrieved. Spec.lean remains unchanged and unproved.


Similarly, the coefficientwise Borel transform B obeys

    F - B(F) = exp(z)-1-z.

Evaluating at 1 yields B(F)(1)=alpha-(e-2). The Borel transform is not a
rational map on the single endpoint value F(1), so it does not propagate
rationality to the new value.

Further differential eliminations would have to be combined with a justified
boundary or simultaneous-approximation construction. In particular, small
residual coefficients by themselves do not provide a nonzero integer linear
form A*alpha-B. No such construction with controlled heights was obtained in
this review. The original Spec.lean is unchanged.
