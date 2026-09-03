# Review of a universal short-shift obstruction

## Status

This review did not settle the conjecture and introduced no new Lean
assertion. Spec.lean remains unchanged with its original sorry.

## Proposed route

A hypothetical limit r_A(n)/log n -> c would give small relative changes
between nearby large targets. For example, mathematically, for every fixed
0<theta<1 the changes r_A(n+d)-r_A(n), uniformly for 0<=d<=n^theta,
would be o(log n). This observation was considered as a way to exploit the
existing short-difference peak theorem. No new formal uniform-shift lemma
was needed or added in this review.

## Why the available peak does not suffice

The verified theorem gives a d<sqrt(N) for which

    #{x<N : x in A and x+d<N and x+d in A} >= gamma (log N)^2.

The centers 2x+d of these pairs vary with x. The theorem does not give a
common sum with that many representations. Moreover, its only substantive
input is the positive counting asymptotic count(A,N)~L sqrt(N log N).
It thus cannot distinguish a witness from other sets with that profile.
The log-squared total can accumulate across many scales without violating
local logarithmic bounds on individual annuli.

Applying the existing convolution-square stability idea to translates
would still require careful control of overlap mass. A fixed-shift overlap
need not be negligible merely from the stated counting profile. Even
favorable overlap estimates feed the known second-moment mechanism at
square-root-logarithmic scale, not at logarithmic scale.

A proposed packing argument based only on many almost-disjoint translates
has no justification here. Finite cyclic near-flat sets already permit
many translated square roots whose self-convolutions are close to the same
constant. No general logarithmic gain from the number of translates can
be assumed. A natural-number, multiscale gain would require a new theorem.

## Remaining gap

The checked universal error-energy bound and its Jensen higher-moment
consequences remain compatible with o(log n) pointwise error. There is no
factorial higher-moment gain, common-sum consequence of the difference
peak, or valid universal logarithmic fluctuation contradiction in hand.
No construction resolving the positive direction was obtained either.
