# Verified obstruction to constant-loss quadratic amplification

This does NOT settle Erdős 773. `Spec.lean` was not modified and still has its
one admission for 0 < epsilon <= 1/3.

## Verified result

`AmplificationBarrier.lean` imports the clean `QuantitativeSquareSieve` module,
not `Spec.lean`. Let M(N) be the actual maximum Sidon-subset cardinality of the
first N positive squares. It proves

    NOT EXISTS c>0, eventually N, c*N*M(N) <= M(N^2).

Equivalently, for each fixed c>0 there are arbitrarily large N with

    M(N^2) < c*N*M(N).

The theorem names, in namespace `Erdos773.Amplification`, are
`no_constant_quadratic_amplification` and
`frequently_small_quadratic_gain`. Their axiom audits contain only propext,
Classical.choice, and Quot.sound. No admissions are used.

## Proof mechanism

Write f(N)=M(N)/N. The already verified dyadic sieve estimate gives

    f(N) <= 2*r^k    whenever 2^((k+3)^2) <= N,
    r=sqrt(3/4)<1.

An eventual recurrence f(N^2)>=c*f(N), started at any sufficiently large
integer B>=2, would imply

    f(B^(2^m)) >= c^m*f(B).

Choose an integer A with r^A<c. For all sufficiently large m,

    (A*m+3)^2 <= 2^m,

so the upper bound at k=A*m gives

    c^m*f(B) <= 2*r^(A*m).

Dividing by c^m and taking m large contradicts f(B)>0. Positivity is proved
using the singleton square subset {1}. The proof uses an elementary bound
m^3<=2^m for m>=10, rather than any unverified asymptotic estimate.

## Scope

This rules out the simple proposed amplification law with a fixed positive
constant at *every* sufficiently large scale. It does not rule out a
scale-dependent subpower loss, nor an amplification law holding only at
selected scales. No such successful construction has been obtained.

Most importantly, it is not a disproof of N^(1-o(1)) growth. For example,
abstract growth of the form N*exp(-sqrt(log N)) is near-linear in exponent
but has M(N^2)/(N*M(N)) tending to zero. This illustrative growth function is
not asserted to equal the actual square-Sidon maximum or to satisfy the
stronger primorial upper bound.

The full-block tensor approach was also reconsidered, but mixed-fiber
collisions remain. Coarse pair matching alone is insufficient, as already
verified in `LiftingObstacle.lean`. No new bound closing the main gap was
obtained from the block constructions.

Verification:

    lake env lean -s 65536 Submission/AmplificationBarrier.lean

Log: /tmp/amplification-barrier.log
