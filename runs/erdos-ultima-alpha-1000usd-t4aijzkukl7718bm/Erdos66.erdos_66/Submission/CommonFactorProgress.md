# Common-factor cylinder counts and the common-period scale budget

## Original task status

The conjecture remains unresolved. Spec.lean is unchanged with its original
sorry, and no proof has been submitted.

## Verified files

* CommonFactorCylinderExplore.lean
* CommonPeriodScaleExplore.lean

Both compile and have current oleans. CommonFactorAudit.lean audits 14
lemmas/theorems using only propext, Classical.choice, and Quot.sound.

## Exact retained-factor calculation

Let P_i be disjoint subsets of a common finite group G, and let B_i subset H
and C_i subset K be arbitrary finite sets in two other finite groups. In
G x (H x K), define

    left  = union_i P_i x B_i x K,
    right = union_i P_i x H x C_i.

At a target (z,y,w), the exact cross count is

    sum_(i,j) r_(P_i,P_j)(z) |B_i| |C_j|.

It does not depend on y,w or on internal representations in B_i,C_j.
The same-side counts are exactly |K| times the old G x H mixed count and
|H| times the G x K mixed count, respectively. Separate self-flatness is
not used to infer the displayed cross count.

The universal palette matrix theorem now gives one fine palette before
all later B,C and all targets, with relative cross error epsilon under the
existing alphabet/height condition. The coarse rank-one kernel has mean

    average_i |B_i| * average_j |C_j|.

These statements are in a product group. No identification of the field
plane with an ordinary cyclic group has been assumed.

## Common-period arithmetic

For positive N and periods d,e, suppose

    N <= x d,   N <= x e,   lcm(d,e) <= B N.

Using d e = gcd(d,e) lcm(d,e), the checked scalar theorem gives

    N <= B x^2 gcd(d,e).

Apply the earlier progression bound to two literal macroscopic repeated
patterns inside a hypothetical witness. It supplies
x=(c+1)log(6N), so averaging over even one O(N)-length common period requires

    N <= B (c+1)^2 log(6N)^2 gcd(d,e).

Thus a common factor must have size Omega(N/log(N)^2), not merely be nontrivial.
A sequence version proves N/lcm(d,e)->0 whenever

    gcd(d,e) log(6N)^2/N -> 0

under the same repeated-pattern hypotheses.

## Limitation

This refines the earlier full-product-period restriction. It does not
exclude arbitrary varying colors, sparse high-block selections, or
constructions without the specified long complete repetitions. Neither
the exact cylinder identity nor this scale restriction supplies a compatible
infinite construction or the negation of the original conjecture.
