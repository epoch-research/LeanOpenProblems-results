# Strictly increasing digit vectors with common first two moments

The original Erdős 773 conjecture remains UNSETTLED. Spec.lean was not
changed; its one sorry remains at line 17287 for 0 < epsilon < 1/3.
The established unconditional endpoint is still eventual M(N) >= N^(2/3).
No incomplete proof was submitted.

## New verified module

Submission/MonotoneDigitMomentCollision.lean imports the clean
PrimeColorCollisions module (whose finite coloring theorem applies to
arbitrary root carriers, not only primes). It builds without warnings or
admissions. Its four printed audits use only propext, Classical.choice,
and Quot.sound. Its olean has been built.

Namespace: Erdos773.MonotoneDigitMomentCollision.
Log: /tmp/monotone-digit-moment.log.

For d >= 100000000000000, let

    H = 2^(d^2), B = (d+1)H.

A word w : Fin d -> Fin H has digits

    digit(w,i) = (i+1)H + w(i).

The digits are positive, strictly increasing, and less than B. The roots
are their ordinary base-B evaluations, hence lie strictly between 0 and
B^d. Canonical radix uniqueness makes the root map injective. There are
exactly H^d roots.

The theorem `collision` supplies four pairwise distinct words with an
actual equal-square-sum collision after evaluation, and equal digit sums
and equal squared digit norms. Injectivity supplies four distinct roots.
The separate theorem `digit_strictMono` applies to every word.

## Proof, not a solver certificate

The two moments are colored by

    Fin(d B+1) x Fin(d B^2+1),

with at most 4 d^2 B^3 colors. The generic four-distinct collision theorem
applies once

    16 d^2 B^3 M(B^d) < H^d.

This is first packaged as the explicit finite hypothesis of
`collision_of_count`. Then `count_gap` proves that hypothesis for all the
displayed d, using the already verified primorial upper bound

    M(N) <= 2 N exp(-log N/(512 log log N)).

The logarithmic estimates are proved in Lean:

    d^2/2 <= log B <= 2 d^2,
    log log(B^d) <= d/16384.

Thus the negative exponential exponent is at least 16 d^2. The logarithm
of the counting prefactor 32 d^2 B^3 (d+1)^d is strictly smaller than this.
There is no admitted large-parameter or numerical asymptotic estimate.

## Exact exploratory test

Research/MonotoneSphereRotation.py encodes a restricted fixed rational
rotation, increasing disjoint digit bands, and equality of the two moments.
The attempted parameters were B=10000, length=12, and

    (p,r,q)=(9999,200,10001), p^2+r^2=q^2.

The solver had an internal 180-second limit and an external 200-second
wrapper. The log contains only the parameter header; no SAT/UNSAT result,
model, or exact witness was returned. The process has ended. No conclusion
is inferred from this run, and the Lean theorem does not depend on it.
Log: /tmp/monotone-sphere-10000-12-100.log.

## Essential scope restrictions

This disproves a blanket assertion that increasing digits plus common
first and second digit moments always give Sidon squares. It does not say
that every moment class is bad, that no large Sidon subclass exists, or
that a proposed criterion fails eventually as the radix grows with a FIXED
dimension. Here dimension and radix grow together.

It is not a disproof of the original conjecture, and it supplies neither a
near-linear construction nor a new exponent for the original maximum.
The large-Gaussian-direction review likewise produced no new useful tail
bound or carrier selection theorem.

## Correction to the carried-forward summary

NearCriticalJointCapacity.near_critical_obstruction has quantifiers

    for every epsilon > 0, there EXISTS a fixed positive g, ...

not 'for every fixed positive g'. In particular it makes no contradictory
capacity-one claim. The actual Lean theorem and its original research notes
already have the correct quantifiers; only the prose compaction summary
was inaccurate on this point.

## Main-file state

Spec.lean SHA-256 remains
257d2e55d464b8ea5a35ca7f1257dc2f52fa771ee4bfdf9b8940.
Its sole import and the original conjecture statement are unchanged.
