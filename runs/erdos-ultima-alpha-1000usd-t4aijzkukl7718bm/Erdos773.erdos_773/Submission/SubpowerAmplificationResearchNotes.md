# Subpower-loss amplification: an exact conditional reduction

This continuation does not settle Erdős 773. The main file is unchanged and
still has its sole admission at line 2031, for 0 < epsilon <= 1/3.

## Verified equivalence

`SubpowerAmplification.lean` imports only `FormalConjecturesUtil`.
Let M(N) denote the actual maximum Sidon-subset cardinality among the first
N positive squares. The theorem

    square_sidon_iff_subpower_amplification

proves equivalence of the exact original proposition with

    for every delta>0, eventually
    N^(1-delta) * M(N) <= M(N^2).

Neither side of this equivalence has been established. In particular the
file does not assume the unproved original theorem or import `Spec.lean`.

The equivalence is first proved abstractly for a monotone real-valued f on
naturals with f(N)>=1 eventually and f(N)<=N:

    nearLinear_iff_subpowerAmplifies.

The reverse implication does not use f(N)<=N. It begins with f(N)>=1.
If f(N)>=N^(1-epsilon) eventually, apply the amplification hypothesis
with delta=epsilon/4. At square indices this supplies exponent

    2 - 5*epsilon/4.

The interpolation lemma yields the eventual bound at every integer N with
exponent 1-3*epsilon/4. Repeated improvement gives gaps (3/4)^k, tending
to zero.

## Interpolation is included

The generic `interpolate_square_lower` proves:

    if f is monotone, 0<=beta<=1, rho>0, and eventually
    f(n^2)>=n^(2*beta+rho), then eventually f(N)>=N^beta.

For s=floor(sqrt(N))>=1 one has s^2<=N<=4*s^2. The slack factor s^rho
eventually exceeds 4, absorbing this interpolation loss. Thus the argument
does not infer a bound for all indices merely from a bound along a sparse
sequence of iterated squares.

The forward implication applies the original lower bound at N^2 with
exponent loss delta/2 and uses M(N)<=N. Monotonicity, the upper bound,
and M(N)>=1 are all proved directly from `Finset.maxSidonSubsetCard`.

## Relationship to earlier work

The fixed-power amplification barrier rules out a fixed positive constant
in place of N^(-delta), even for theta=1. The present equivalence shows
precisely why allowing a subpower loss would be sufficient. It does not
supply such a loss bound.

The factor-pair selection route was reviewed again, but no compatible
near-linear vertex selector emerged. Selecting one representation of each
square difference still does not ensure that all pairs of a large root set
use those choices. No main-gap exponent was improved.

## Verification

All three printed axiom audits contain only propext, Classical.choice,
and Quot.sound. The file has no admissions and builds with

    lake env lean -s 65536 Submission/SubpowerAmplification.lean

Log: `/tmp/subpower-amplification.log`.
Main-file check: `/tmp/spec-subpower-amplification-check.log`.
No proof submission has been made.
