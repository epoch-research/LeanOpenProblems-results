# Shifted original-series poles (verified auxiliary work)

This is not a settlement of Erdős 68. Submission/Spec.lean remains unchanged
with its original sorry. No proof or disproof has been submitted.

## Verified file

Submission/ShiftedPoleKernels.lean compiles without warnings and has a built
olean. All seven printed axiom audits contain only propext, Classical.choice,
and Quot.sound. The auxiliary file has no holes or added axioms.

## Exact shifted-pole identity

For n>=j+2, let (n)_j=n(n-1)...(n-j+1). The verified theorem
`factorial_shifted_pole` states

    (n)_j / (n!-(n)_j) = 1/((n-j)!-1).

Thus falling-factorial poles really do recover shifted original summands;
they are not the factorial-power moments used in the earlier polynomial
kernel construction.

The verified `two_pole_identity` combines adjacent poles:

    (A-k)/(x-1) + n*h/(x-n)
      = [(A+n*h-k)*x + n*(k-h-A)] / [(x-1)*(x-n)].

It assumes both displayed denominator factors nonzero.

## Exact telescoping boundary

`hasSum_shifted_kernel` allows any rational sequence g whose real casts are
summable. If g(0)=A-B, then

    sum_(n>=0) [A*term(n+1)+g(n)-g(n+1)] = A*alpha-B.

Here term(n)=1/((n+2)!-1). This is an exact identity, not a bound or a
nonvanishing assertion. In a polynomial shifted-pole ansatz one would take
g(n)=H(n+2)/((n+2)!-1). The file does not separately package the summability
of that specialization as a theorem.

## Obstruction to exact first-column cancellation

For a rational polynomial H define the already-verified column coefficient

    L_j H(n)=n^j H(n-1)-H(n),  j>=1.

`constant_column_zero` proves that L_j H(n)=A at every original row n>=2
forces A=0. The proof uses the established telescoping identity and the
irrationality of the individual factorial-power sum E_j: otherwise
A*E_j=H(1) would be rational.

`eventually_constant_column_zero` proves the same conclusion if the
coefficient is constant only after an arbitrary finite cutoff. Polynomial
identity on infinitely many natural arguments reduces this to the previous
result.

For the two-pole numerator, `two_pole_leading_nonzero_after` consequently
proves that, for A!=0 and every cutoff, some later row has

    A+n H(n-1)-H(n) != 0.

Thus this fixed-polynomial two-pole ansatz cannot identically cancel its
entire leading 1/n! column, even eventually.

## Scope limitations

This is not nonvanishing of the TOTAL original-series linear form.
It does not rule out approximate cancellation, a growing family of
polynomials, more general rational functions of the row index, or kernels
with additional poles. No useful simultaneous bound on the integral
boundary, analytic error, and nonvanishing has been obtained.

No complete informal solution is awaiting formalization. The conjecture
remains unproved and undisproved in this work.
