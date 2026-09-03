# Pointwise transfer and balanced ratio sampling — no settlement

The original conjecture remains UNSOLVED. `Submission/Spec.lean` is unchanged,
including its original `sorry`. No proof or irrational counterexample was
found in this continuation, and no incomplete proof was submitted.

## Existing exact transfer results rechecked

`ReciprocalPrimePairs.lean` already proves that for alpha>1 irrational and
n>0, with q=floor(alpha*n),

    floor(q/alpha)=n-1,   ceil(q/alpha)=n.

Reciprocal exchange is therefore not an invariance of the floor-prime-pair
conjecture. Restricting the fractional-part window does not remove this
rounding direction.

`RationalRoute.lean` already proves transfer from a rational approximant
r=a/b when the prime input satisfies 8p<=b^2 and r*p lies between q+1/4 and
q+3/4 for a prime q. The finite arithmetic estimate supplying such p,q is
an explicit unproved hypothesis in that file. No estimate establishing it
was found here. No new equivalent conditional criterion was added.

`RationalObstruction.lean` already rules out a fixed local congruence
obstruction at reduced noninteger rational slopes. It chooses determinant
one, or determinant two when both numerator and denominator are odd, and
checks the parity condition as well as the odd-prime local conditions.
This is not a simultaneous-primality theorem.

## Informal balanced ratio-sampling calculation

A possible metric-to-pointwise route was reviewed, without a new Lean
claim or sufficient bound. In a balanced off-diagonal block with all four
factors of order M, fix the prime factors p,q. The remaining condition is

    k <= (alpha*p/q)*m < k+1/q.

The inner sequence is not an ordinary full-width Beatty correlation: its
fractional-part window has width 1/q. For m,k of order M this requires
logarithmic frequency resolution of order M*q, which is of order M^2 in
the balanced case. Meanwhile the possible ratios p/q have spacing on the
order of 1/M^2. Thus these samples are at the critical resolution, not a
uniformly denser sampling mesh. A continuous mean-square estimate cannot
simply be substituted for the discrete sum over these prime ratios.

Equivalently, for a fixed balanced p,q, the expected number of m,k in the
strip is only of constant order. There is no long inner sum in which one
can assume cancellation before averaging over the prime factors.

This is a limitation of that proposed argument, not a general theorem
excluding all ratio-sampling approaches. It supplies neither the signed
lower gap needed by the existing reduction nor a prime-pair lower bound.
