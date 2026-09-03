# Repair capacity with shared points

## Original conjecture status

The conjecture in Submission/Spec.lean remains unresolved. That file is
unchanged, still with its original sorry. No proof or disproof was submitted.

## Checked new results

BoundedReuseRepairExplore.lean compiles and has a current olean. Its namespace
is Erdos66BoundedReuseRepair.

### Incidences rather than distinct packets

For any finite packet family P_i contained in B intersect [0,N), if every
point belongs to at most L packets, then

    sum_i |P_i| <= L count(B,N).

No disjointness of packets, predecessor map, or sampling assumptions are
required. In particular, if each packet has at least d real-valued units
of cardinality, then

    d * number_of_packets <= L count(B,N).

This generalizes the earlier disjoint-cell capacity restriction to controlled
point reuse. It does not repeat the old disjoint-cell theorem as a new result.

### Scale-dependent reuse and a global logarithmic envelope

Suppose B has

    r_B(z) <= K + C log(z+2),    K,C >= 0.

For packets supported below 2N, each of size at least delta log N, with
maximum point reuse L, the checked inequality is

    delta^2 log N * number_of_packets^2
      <= 4N (K+4C) L^2

once N>=2 and log N>=1.

Consequently, even if the permitted reuse L(N) grows with N, the condition

    L(N)/sqrt(log N) -> 0

forces

    number_of_packets(N)/sqrt(N) -> 0.

Main names:

* packet_incidence_bound
* uniform_packet_incidence_bound
* logarithmic_packet_reuse_bound
* slowly_reused_packet_count_zero

### Sharper restriction for a same-coefficient monotone completion

If A subset B and both counting functions divided by R(N) tend to the same
finite limit, then

    count(B\A,N)/R(N) -> 0.

Packets consisting of new points, with a FIXED bound on point reuse, must
therefore have negligible total charged mass:

    d(N) * number_of_packets(N)/R(N) -> 0.

Specialize to a hypothetical witness B with coefficient c!=0 and a base A
whose counting function already has the necessary profile

    count(A,N)/sqrt(N log N) -> 2 sqrt(c/pi).

The checked Tauberian theorem gives that same limit for B. If each new-point
packet costs at least delta log N, then bounded reuse forces

    number_of_packets(N) * sqrt(log N)/sqrt(N) -> 0.

The base counting-profile hypothesis is explicit. No arbitrary base is
silently assumed to have it, and no completion is constructed.

Main names:

* added_count_limit_zero
* bounded_reuse_packet_mass_zero
* same_coefficient_completion_packet_mass_zero
* same_coefficient_completion_target_count_zero

## Verification

BoundedReuseRepairAudit.lean checks all eight principal declarations. Only
propext, Classical.choice, and Quot.sound occur. The production file contains
no sorry or added axiom.

## Scope and remaining problem

This rules out trying to overcome the square-root packet-capacity restriction
by allowing only bounded reuse, or reuse little-o of sqrt(log N) in the stated
regime. It does not rule out unrestricted sharing, more global signed changes,
or a different infinite construction.

It also does NOT prove that the exceptional sets of the previously constructed
base actually violate these necessary bounds: the available upper estimates
on those exceptional sets are insufficient to verify the repair hypotheses,
not lower bounds demonstrating that every such repair must fail.

No point-reusing correction scheme that handles those exceptions with uniform
o(log n) collateral was obtained. No compatible change-of-modulus construction
or universal contradiction was proved. The original conjecture is still open
in this workspace.
