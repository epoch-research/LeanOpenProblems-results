# Boundary polynomial nonvanishing

## Original task status

The conjecture in Submission/Spec.lean remains neither proved nor disproved.
The file is unchanged with its original sorry, statement, and import. No
proof or disproof has been submitted. Its SHA256 remains

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## New verified necessary condition

Let A,c be a hypothetical witness, c nonzero, and let

    F_A(r) = sum_n 1_A(n) r^n.

For EVERY nonzero bivariate polynomial P with real coefficients,

    P(r,F_A(r)) != 0

for all r sufficiently close to 1 from below. The threshold can depend on
P. In particular no fixed nonzero polynomial identity holds in a whole
left-neighborhood of r=1.

This is stated using actual Mathlib bivariate polynomials:

    Erdos66BoundaryMvPolynomial.witness_eval_ne_zero

has P : MvPolynomial (Fin 2) Real, assumes P != 0, and concludes eventual
nonvanishing of MvPolynomial.eval ![r,series (indicator A) r] P.

There is also a boundary-distance version with ![1-r,F_A(r)], and a finite
monomial-sum version in Erdos66LogBoundaryPolynomial.

## Direct asymptotic proof

The existing Abelian theorem gives, after 1-r=exp(-s),

    F_A(1-exp(-s)) / [exp(s/2) sqrt(s)] -> sqrt(c) != 0.

A monomial (1-r)^i F_A(r)^j therefore has asymptotic scale

    exp((j/2-i)s) s^(j/2),

with nonzero limiting multiplier c^(j/2). Among any finite collection of
distinct pairs (i,j), choose the greatest exponential weight j/2-i, then
the greatest j among ties. This picks a unique dominant monomial:

* lower exponential weights are negligible against any fixed power of s;
* equal exponential weights with lower j are negligible by a negative
  power of s.

After division by the dominant scale, the polynomial tends to its nonzero
dominant coefficient times the nonzero multiplier. This proves eventual
nonvanishing without assuming a Puiseux expansion or an algebraic-function
classification theorem.

The generic dominance theorem works for any real function with the displayed
exponential/square-root asymptotic. The conversion to MvPolynomial uses the
bijection between Fin 2 exponent vectors and pairs of natural exponents.
The substitution X_0 -> 1-X_0, X_1 -> X_1 is explicitly proved involutive,
so the distance-to-boundary and original-argument formulations are equivalent.

## Files and verification

All three production files compile with current oleans:

* ExpPowerDominanceExplore.lean
* LogBoundaryPolynomialExplore.lean
* BoundaryMvPolynomialExplore.lean

LogBoundaryPolynomialAudit.lean audits eleven principal declarations.
LogBoundaryPolynomialAudit.log reports only propext, Classical.choice, and
Quot.sound. No production placeholders or new axioms were introduced.
LogBoundary*Checks*.lean files are API scratch files, not dependencies.

## What the analytic review does NOT establish

This is not a contradiction for Boolean power series: such series need not
be algebraic. After establishing the radial asymptotic, the proof does not
use Boolean coefficients at all. Thus the same dominance mechanism applies
to the corresponding non-Boolean fractional model.

The review did not establish analytic continuation, a forbidden zero
location, a universal logarithmic-size coefficient fluctuation, or a
coefficientwise square-root transfer. In particular, the existing universal
squared-error scale N log N is still compatible with the conjecture's
allowed o(N log^2 N) squared-error scale. No unwarranted upgrade from
coefficient error o(log n) to bounded, summable, or analytically continuable
error has been made.

No infinite construction or universal contradiction settling Spec.lean has
been obtained in this continuation.
