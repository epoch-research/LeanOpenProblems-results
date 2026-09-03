# Rising Charlier factors in monic row kernels

This is an external exact finite construction test, not a Lean theorem or a
settlement of Erdős 68. `Spec.lean` is unchanged with its original `sorry`.

## Family and motivation

Let R_k(x)=(x+1)...(x+k)-1. For a positive integer c define

    C_(N,c)(x)=sum_(j=0)^N (-c)^(N-j) choose(N,j) x^(overline j),
    P_(K,N,c)(x)=(product_(k=1)^K R_k(x))*C_(N,c)(x).

These are integer polynomials. The construction computes C by

    C_0=1, C_1=x-c,
    C_(n+1)=(x+n-c)*C_n+c*n*C_(n-1).

Its exponential generating function is exp(-c*t)*(1-t)^(-x). In particular,
at negative integral x the rising-factorial expansion terminates. This
motivates testing it near the negative-integer clusters of the monic row
polynomials. No general sign estimate for the resulting errors is assumed.

The already verified `RisingMonicForms.integer_form_identity` applies to
these integer polynomials. Set

    A=P(1), B=sum_(k=1)^(degree P) (P div R_k)(1).

Every polynomial quotient/remainder is checked exactly. The pair (A,B) is
then divided by its gcd; its sign is chosen to make A nonnegative.

## Completed construction

For K=1,...,12, the distinct N values are

    0, K, 2K, K(K+1)/2, K^2, 2K^2.

For K=0 use N=0,2,3,4,6,8,12,16,24,32,48,64,96,128. At N>0 the distinct
c values are 1,2,max(1,floor(N/4)); at N=0 only c=1 is used.

All 192 cases complete. The exact error enclosure uses W=2000! and

    L=sum_(n=2)^2000 floor(W/(n!-1)),
    L/W < alpha < (L+2002)/W.

Thus the full original-series tail is retained, rather than only a finite
row approximation. Classifications are all exact rational comparisons:

* 80 errors greater than 1;
* 103 errors less than -1;
* 5 errors in (0,1);
* 3 errors in (-1,0);
* 1 constant form equal to -1;
* no ambiguous interval classifications.

The eight small cases, listing (K,N,c,A,B) after pair reduction, are

    (0,2,1,1,1), (0,3,1,1,1), (1,0,1,1,1),
    (2,0,1,5,7), (2,2,2,1,2), (2,3,1,2,3),
    (2,4,2,5,6), (3,0,1,115,144).

Every tested K>=4 has absolute reduced error greater than one. This is a
finite statement only; no asymptotic obstruction or irrationality claim
follows. At (K,N,c)=(12,288,1), for example, the reduced coefficient A has
2120 bits and the diagnostic logarithm of the absolute error upper bound
is about 610.877 in base ten.

## Artifacts and independent audit

Construction:

* `/tmp/rising_charlier_forms.py`
* `/tmp/rising_charlier_forms.log`
* `/tmp/rising_charlier_forms.json`

Audit:

* `/tmp/rising_charlier_forms_audit.py`
* `/tmp/rising_charlier_forms_audit.log`

The independent audit reconstructs C by its explicit binomial sum, rather
than its recurrence. It computes Laurent coefficients a_m of U(x)=sum 1/R_k(x)
by the reciprocal-series recurrence, rather than by polynomial division.
For P=sum p_j*x^j it then verifies the boundary using

    B=sum_(j>=1) p_j * sum_(m=1)^j a_m.

This is a finite formal-series calculation, not an assumption that the
Laurent expansion converges at x=1. The audit also checks both raw
coefficients, their gcd reduction, every rational error interval, and every
classification. All 192 audits passed. Both processes have completed; no
calculation remains running.

No family of nonzero integer forms tending to zero has been obtained, and
no proof or disproof of the original conjecture has been submitted.
