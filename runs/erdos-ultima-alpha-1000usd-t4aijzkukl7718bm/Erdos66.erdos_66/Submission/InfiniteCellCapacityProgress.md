# Infinite predecessor compatibility and packet capacity

## Status

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged, with its original sorry. No completed proof has been submitted.

## Infinite compatibility (checked)

`InfinitePredecessorReplacementExplore.lean` defines

    replacement(A,F) = (A \ predecessor(A) '' F) union F

for an arbitrary, possibly infinite inserted set F.

Assume F is disjoint from A, every predecessor of a point of F belongs to A,
and predecessor(A) is injective on the ENTIRE F. Then

    -1 <= count(replacement(A,F),N) - count(A,N) <= 0

for every N. The bound is one globally, not one per packet.

Proof: the active set

    {u in F : predecessor(A,u) < N}

is finite, by injection into [0,N). Replacing just this finite set agrees
with the full infinite replacement below N, so the already checked finite
prefix theorem applies. The same observation gives a finite attainment
lemma for each individual representation count. This is not a selection
or collateral-convergence theorem.

Main declarations in namespace `Erdos66InfinitePredecessorReplacement`:

* active_finite
* finite_replacement_agrees
* infinite_replacement_prefix
* infinite_replacement_discrepancy
* finite_replacement_representation

## Capacity of disjoint packets (checked)

`PredecessorPacketCapacityExplore.lean` proves that a finite inserted set F,
with points below N and distinct old predecessors, satisfies

    |F| <= count(A,N).

For pairwise disjoint packets P_i using distinct original cells globally,

    sum_i |P_i| <= count(A,N).

If every packet has at least d>0 points and r_A(z)<=K+C log(z+2), C>=0,

    number_of_packets
      <= sqrt(2N (K+C log(2N+2))) / d.

This bound is geometric; it does not depend on a union-bound estimate or
on the finite selection algorithm.

For an eventual family of packets with support below 2N, with at least
`delta log N` points in each packet for a fixed delta>0, the theorem
`packet_count_div_sqrt_zero` proves

    number_of_packets(N) / sqrt(N) -> 0.

The hypotheses include pairwise disjointness of the packet supports and
injectivity of the predecessor map on their union. The original set A
has a fixed global logarithmic representation envelope, with K,C>=0.
The proof uses

    count(A,2N)^2 <= 4N (K+4C) log N

for sufficiently large N and then bounds the squared normalized packet
count by a constant divided by log N.

## What follows, and what does not

This supplies a genuine infinite prefix-compatibility lemma, but shows why
simply concatenating the existing disjoint packets cannot handle exception
families denser than the square-root scale. The known weak positive power
saving for the constructed base does not imply the required sparseness.

It does NOT establish that the actual exceptional sets must be dense, nor
that all possible count-preserving methods have this capacity restriction.
In particular, deliberately reusing an inserted point in the repairs of
several centers violates pairwise packet disjointness and is not excluded.
No general impossibility statement about the original existential
conjecture has been obtained.

The remaining serious directions are stronger structural control on a base,
a point-reusing correction scheme with proved all-target collateral bounds,
or a compatible finite-template construction through scale changes.
No new such construction was found in the accompanying review.

## Verification

Both production files compile and have current oleans. The main declarations
are audited in `InfinitePredecessorAxiomCheck.lean`; only propext,
Classical.choice, and Quot.sound occur. There are no placeholders or new
axioms in the two production files. Name-search scratch check files may
contain failed #check commands and are not production dependencies.
