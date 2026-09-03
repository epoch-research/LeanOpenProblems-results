# Balanced floor-strip multiplicity — still no settlement

The original conjecture in Spec.lean remains unchanged and unproved. No
irrational counterexample or sufficient signed lower bound was obtained.

## New verified helper

`FloorPrimeDeterminant.lean`, namespace `Erdos972FloorPrimeDeterminant`, compiles
with only propext, Classical.choice, and Quot.sound in the principal audits.

`cross_products_eq` proves the following exact statement. Suppose alpha>0,
m,q,s>0, q,s <= alpha*m, and

    k*q = floor(alpha*m*p),
    k*s = floor(alpha*m*r).

Then p*s = r*q. Indeed, putting the two floor errors in [0,1),

    -q < alpha*m*(p*s-r*q) < s.

The assumptions q,s <= alpha*m put the integer determinant strictly between
-1 and 1. No irrationality or primality assumption is needed for this step.

`prime_ratio_alternatives` proves that if p,q,r,s are primes and p*s=r*q,
then either (p,q)=(r,s) or p=q and r=s.

`non_diagonal_pair_unique` combines these: for each fixed outer pair (m,k),
there is at most one non-diagonal prime pair in the stated range. The
multiplicative diagonal p=q is a genuine exception and is not discarded.

## Remaining limitation

This is a multiplicity statement, not a signed estimate. The coefficients
on the many different outer pairs can still have either sign. Even a
zero-one incidence restriction on the non-diagonal terms does not imply
cancellation against the actual divisor coefficients. No spectral bound,
prime-pair lower bound, or strict four-factor lower gap was deduced.

The final submission file has not been changed or resubmitted as complete.
