# Rational auxiliary functions do not allow exact constant-column cancellation

This is auxiliary progress, not a proof or disproof of Erdős 68.
Submission/Spec.lean remains unchanged with its original sorry. Nothing has
been submitted.

`RationalFunctionColumn.lean` compiles without warnings, has a built olean,
and its three printed axiom audits use only propext, Classical.choice and
Quot.sound.

## Pure denominator argument

Let P,Q be coprime rational polynomials. If

    X^j P(X-1) Q(X) - P(X) Q(X-1) = A Q(X-1) Q(X),

then Q divides P(X)Q(X-1), hence Q divides Q(X-1). Translation preserves
both degree and leading coefficient, so Q(X-1)=Q(X). Evaluating at natural
numbers gives Q(n)=Q(0) for every n; polynomial identity on infinitely many
points then gives Q=C(Q(0)).

This is `denominator_constant`. It is a polynomial-arithmetic statement and
does not use irrationality of the original sum or of a factorial-power sum.

## Eventual rational-function column statement

For j>=1, let H=P/Q be reduced with Q nonzero. Suppose at every sufficiently
large natural row n,

    n^j H(n-1)-H(n)=A,

where A is rational. Nonzero Q has only finitely many natural roots. Clearing
denominators outside those roots gives the polynomial identity above, so
Q is constant. The previously verified polynomial-column obstruction then
implies A=0. That last obstruction uses irrationality of the individual
factorial-power sum, not the unproved irrationality of the original series.

The main theorem is `rational_function_constant_column_zero`; the Lean
exponent is j+1 and the original row index is n+2. A separate version
`eventually_constant_column_zero` has an explicit eventual no-pole hypothesis.

This rules out exact nonzero constant-column cancellation by any fixed
reduced rational auxiliary function, not merely by a polynomial. It does
not exclude approximate cancellation or a growing family of kernels, and
it gives no nonvanishing or smallness theorem for their TOTAL forms against
the original sum. No complete proof or disproof was obtained.

## Other review in this pass

The exact modified-Engel arithmetic was reconsidered. Cancellation remains
controlled by the square of the new reciprocal denominator, not by the old
factorial base, so no integer descent or exclusion of the exact consecutive
multipliers was established. No new numerical search was performed.
