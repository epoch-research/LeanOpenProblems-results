# Rank-one original-tail Toeplitz determinants

This is a mathematical construction and an external exact finite test, NOT
a Lean theorem or a settlement of Erdős 68. Spec.lean is unchanged with its
original sorry. No complete proof or disproof has been obtained.

## Positive matrices with affine determinants

Write S_h=sum_(n=2)^h 1/(n!-1), with S_1=0. For K>=1 and N>=2 define

    M_(N,K)(X)_(i,j)=X-S_(K+|i-j|),  0<=i,j<N.

The retained X matrix is the all-ones matrix J and has rank one. This
construction differs from the earlier polarized quadratic ansatz and from
the full-rank factorial-scaled Hankel matrices.

Put s=S_(K+N-1) and C_(i,j)=s-S_(K+|i-j|). Then

    M(X)=C+(X-s)J.

C is rational and positive definite. To see this, put

    t_l=1/((K+l)!-1),
    G_l(i,j)=max(0,l-|i-j|).

G_l is the Gram matrix of the indicator vectors of the integer intervals
[i,i+l), so it is positive semidefinite and G_1=I. Direct telescoping gives

    C=sum_(l=1)^(N-2) (t_l-t_(l+1))*G_l + t_(N-1)*G_(N-1).

All coefficients are positive. When N=2, C=t_1 I; when N>=3, the first
summand is (t_1-t_2)I. This proves positive definiteness for every indicated
K,N, without an assumption about irrationality.

With u the all-ones column, set a=u^T C^(-1)u>0. The rank-one determinant
identity gives

    D_(N,K)(X)=det C * (1+(X-s)*a).

Its leading coefficient is positive and its unique root is

    r_(N,K)=s-1/a < s < alpha.

Thus its positive primitive integer normalization is A*X-B, where B/A is
r_(N,K) in lowest terms and A>0, and

    A*alpha-B=A*(alpha-s)+A/a>0.

The determinant degree remains one. Consequently errors tending to zero
would suffice, with no increasing-degree denominator condition. The issue
is the size after primitive integer normalization, not nonvanishing.

These all-index matrix arguments are informal here, not Lean declarations.

## Exact finite construction and independent audit

Parameters: N=2,...,16 and K in {1,2,4,N}, with duplicates removed.
All 58 cases completed. EVERY primitive integer form has value greater
than one at the full original sum. This finite result is not an asymptotic
impossibility theorem and excludes no other matrix family or parameters.

Construction computes D(0),D(1),D(2) by rational determinants, checks the
positive affine slope and the third value, and reduces the rational root.
Artifacts:

* /tmp/original_tail_toeplitz.py
* /tmp/original_tail_toeplitz.log
* /tmp/original_tail_toeplitz.json

The independent audit uses Python Fraction, not Sage determinant algorithms.
It reconstructs C and an exact positive LDL factorization, checks every
entry of that factorization, solves C*x=u by triangular substitution, and
checks C*x=u. It recovers det C, a=sum x_i, both polynomial coefficients,
and the reduced pair from the preceding rank-one formula.

* /tmp/original_tail_toeplitz_audit.py
* /tmp/original_tail_toeplitz_audit.log

The construction encloses alpha using Ngrid=1200 and

    W=Ngrid!, L=sum_(n=2)^Ngrid floor(W/(n!-1)),
    L/W < alpha < (L+Ngrid+2)/W.

The audit recomputes the enclosure with Ngrid=1217, checks containment in
the stored intervals, and verifies all 58 primitive errors exceed one.
No floating-point value is used as a certificate premise. Both processes
have completed; nothing remains running.

For orientation only, at (N,K)=(16,16) the primitive retained coefficient
has 6310 bits, and the diagnostic log2 of its error is about 6256.93.
The exact rational interval, rather than this diagnostic, proves error>1.

## Why raw rank-one determinant decay is still insufficient

A separate elementary rational comparison uses

    R_N(i,j)=2^(-|i-j|),
    M_N(X)=R_N+(X-1)J.

At X=1 it is positive definite and has determinant (3/4)^(N-1), which tends
to zero. The standard tridiagonal inverse of R_N gives
u^T R_N^(-1)u=(N+2)/3. Hence

    det M_N(X)=(3/4)^(N-1) * [(N+2)X-(N-1)]/3.

After primitive integer normalization the polynomial is

    [(N+2)X-(N-1)]/gcd(N+2,N-1),

whose value at X=1 is 3/gcd(3,N-1), always at least one. This is explanatory
algebra, not a new Lean theorem or a counterexample to Erdős 68. It shows
that rank-one retained coefficients and positive raw determinants tending
to zero do not, by themselves, resolve the normalization problem.

No growing family of small primitive integer forms for alpha was obtained.
The conjecture in Spec.lean remains unproved and undisproved, and no
submission check was made.
