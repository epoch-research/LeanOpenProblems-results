# Monic rising-factorial polynomial-part kernels

This is mathematical analysis and an exact external finite test, not a
Lean-verified settlement. Spec.lean is unchanged with its original sorry.

## An integer-boundary construction

Let

    R_k(x) = product_(i=1)^k (x+i)-1  (k>=1),
    U(x) = sum_(k>=1) 1/R_k(x),
    U(1) = alpha.

For an arbitrary polynomial P in Z[x] of degree M, divide by each monic
R_k using polynomial division over Z:

    P = R_k Q_k + T_k,  deg T_k < k.

For k>M the quotient is zero and T_k=P. Consequently, putting

    A=P(1), B=sum_(k=1)^M Q_k(1),

both A and B are integers, and the exact identity is

    A alpha-B
      = sum_(k=1)^M T_k(1)/R_k(1)
        + A sum_(k>M) 1/R_k(1).

Only a finite sum and the original convergent tail occur; this identity
does not require interchanging an asymptotic expansion with an integral.
In contrast to the geometric Lambert-row operator previously tested,
there is no additional rational boundary denominator to clear.

Take specifically

    P_K = product_(k=1)^K R_k,
    M=K(K+1)/2,
    A_K=product_(k=1)^K ((k+1)!-1).

The first K remainders vanish. Nonvanishing, sign, and smallness of the
remaining total error still require proof; integer boundary alone does
not supply them.

## Completed exact finite test

The script computes the polynomial divisions with integer arithmetic and
bounds alpha using W=1000! and

    L=sum_(k=2)^1000 floor(W/(k!-1)),
    L/W < alpha < (L+1002)/W.

Artifacts:

    /tmp/rising_monic_kernel.py
    /tmp/rising_monic_kernel.log
    /tmp/rising_monic_kernel.json

The first three pairs (A_K,B_K) are (1,1), (5,7), (115,144). Their errors
are certified nonzero and strictly between -1 and 1. At K=4 the pair is
(13685,17219), with negative error of magnitude greater than 64.
All tested K=4,...,16 have absolute error greater than one; the error signs
are not uniformly alternating. At K=16 the integer A has 347 bits, while
the absolute error is about 10^145.878 (a floating-point diagnostic, not
the certificate). The interval classifications themselves use exact
rational arithmetic.

The test completed; nothing is running. These finite failures do not
prove an asymptotic obstruction or exclude other choices of P. No family
with simultaneously controlled integer coefficients, nonzero error, and
error tending to zero has been obtained. There is no complete informal
proof awaiting formalization, and no proof or disproof has been submitted.

## Lean verification of the exact identity

`Submission/RisingMonicForms.lean` now compiles without warnings and has a
built olean. All four printed principal axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Its index n corresponds to R_(n+1) above. The file verifies:

* `rowPolynomial_monic`, `rowPolynomial_natDegree`, and
  `rowPolynomial_eval_one`;
* vanishing of polynomial quotients beyond the polynomial degree;
* `hasSum_residueRows` and `integer_form_identity`, with integer coefficient
  P(1) and integer finite quotient boundary;
* `productKernel_initial_rows_zero`, for the product construction;
* `zero_row_implies_dvd`: any exactly zero row forces (n+2)!-1 to divide P(1).

The last statement uses integral polynomial coefficients and must not be
extended to unrestricted rational kernels. No sign or smallness theorem
for a growing family has been established. The numerical test above remains
an external exact calculation, not a Lean theorem. Spec.lean is unchanged.

## Completed diagonal Padé test for the same parameter function

A separate exact test used the formal expansion

    U(1/z) = sum_(k>=1) z^k /
                (product_(i=1)^k (1+i*z)-z^k)
            = sum_(m>=1) a_m*z^m.

Its first coefficients, including a_0, are

    0,1,1,-2,3,-5,17,-85,388,-1499,5007,-15454,52475,-241919,1393895.

For each N=1,...,24 the test solves for p_N=1 and rational p_0,...,p_(N-1)
with sum_(i=0)^N p_i*a_(r+i)=0 for r=1,...,N. It clears the polynomial
coefficient denominators, then forms the integers

    A=sum_i p_i,
    B=sum_(i=1)^N p_i*sum_(m=1)^i a_m.

The pair (A,B) is reduced by its gcd and A is made positive. The test checks
the linear equations exactly and certifies the error with the same W=1000!
factorial-grid enclosure as the product-kernel test. It does not assume
convergence of the formal series at z=1.

N=1 gives A=0, B=1 and is discarded. N=2 gives (A,B)=(9,11), with positive
error less than one. Every degree N=3,...,24 has absolute error greater than
one. Some errors are negative, so there is no observed uniform sign. At N=24
the reduced A has 953 bits and the diagnostic log10 absolute error is about
274.664493. No small-error family or asymptotic impossibility theorem follows.

Completed artifacts:

    /tmp/rising_monic_pade_fast.py
    /tmp/rising_monic_pade_fast.log
    /tmp/rising_monic_pade_fast.json

The original script used symbolic Matrix.inv and was stopped after the
replacement exact rational DomainMatrix.lu_solve computation had completed.
Its partial log agrees with the replacement on all completed degrees. The
replacement rechecks every equation. No Padé computation remains running.
The final conjecture file is unchanged; no proof or disproof was obtained.

## Later distinct test: added rising-factorial zeros

RisingProductShiftedNotes.md records the completed exact test of
P=(product_(k=1)^K R_k)*(product_(i=0)^(N-1)(x+s+i)), with s=0,1 and both
linear and quadratic choices of N. Among 100 reduced-pair tests, all 77
with K>=4 have absolute error greater than one. This is finite evidence
only, not an asymptotic theorem. The added factors did not supply a useful
growing family, and Spec.lean remains unsettled.
