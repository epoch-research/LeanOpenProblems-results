# Exact correlation renewal — conjecture still unresolved

`Spec.lean` remains unchanged with its original `sorry`. No prime-pair lower
bound or irrational counterexample has been obtained. No incomplete proof
was submitted as a settlement.

## Verified addition

`PrimeCorrelationRenewal.lean`, namespace
`Erdos972PrimeCorrelationRenewal`, compiles. Its three principal identities
audit with only `propext`, `Classical.choice`, and `Quot.sound`.

Write

    C(alpha,N) = sum_{1<=n<=N} Lambda(n) Lambda(floor(alpha*n)),
    W(alpha,N) = sum_{1<=n<=N} log(n) Lambda(floor(alpha*n)).

The file proves the exact finite identities

    W(alpha,N) = sum_{1<=m<=N} C(alpha*m, floor(N/m)),
    C(alpha,N) = sum_{1<=m<=N} mu(m) W(alpha*m, floor(N/m)),

and, for N>0,

    W(alpha,N) - sum_{2<=m<=N} C(alpha*m, floor(N/m)) = C(alpha,N).

The sums retain every cofactor, and the natural-floor multiplication identity
is proved explicitly. No prime-pair asymptotic is used.

## What the review did not establish

The positive renewal identity does not propagate finiteness at alpha to the
other slopes alpha*m. Its inverse restores signed Mobius coefficients and
requires a uniform estimate that has not been proved. One-prime estimates
for each fixed dilate cannot be summed over the full moving cofactor range
without further control.

A possible inverse theorem for the balanced four-factor strip

    |alpha*a*b - c*d| < 1

was also reconsidered. No such theorem has been proved. At the critical
factor length M and frequency range M^2, the fourth-moment energy contains
nontrivial high-frequency mass even when individual Mellin coefficients
are small. Rational rescaling diagonals explain some obstructions, but
excluding them does not itself prove an inverse principle. Interpreting
this as an irrational quadratic-form counting problem supplies no available
weighted equidistribution theorem for the actual coefficients.

The original arithmetic gap is unchanged. These exact identities are not
a proof or disproof of the conjecture.
