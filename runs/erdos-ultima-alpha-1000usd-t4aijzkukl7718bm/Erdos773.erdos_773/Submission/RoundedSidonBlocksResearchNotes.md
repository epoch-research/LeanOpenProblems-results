# Rounded ordinary Sidon marks: separated square blocks

This continuation does NOT settle Erdős 773. Spec.lean is unchanged, with its
sole admission at line 17287 for 0 < epsilon < 1/3. The established endpoint
remains eventual M(N) >= N^(2/3). No incomplete proof was submitted.

## New verified module

`RoundedSidonBlocks.lean` imports the clean OrderedCollisionDefect and
PartialResidueFibers modules. It has no admissions or warnings and builds
with an olean. All eight printed audits use only propext, Classical.choice,
and Quot.sound. Log:

    /tmp/rounded-sidon-blocks.log

Namespace: `Erdos773.RoundedSidonBlocks`.

## Construction and rounding bounds

Let L>0, H>=0, and let A be an ORDINARY INTEGER Sidon set contained in [0,L].
This hypothesis is Sidonness of the marks themselves, not their squares.
Define

    S = 1024 L (H+1)^2,
    center(a) = floor(sqrt(S*(L+a))),
    block(a) = [center(a), center(a)+H],
    values(a) = {n^2 : n in block(a)}.

The module proves

    32 L(H+1) <= center(a) <= 64 L(H+1),

and, for every root n in the a-th block, both inequalities

    S*(L+a) <= n^2 + E,
    n^2 <= S*(L+a) + E,
    E = 130 L(H+1)^2.

Since 4E<S, an equality x^2+y^2=z^2+w^2 forces equality of the sums of the
corresponding marks. Ordinary Sidonness then identifies the unordered pair
of block labels. This is an exact integer rounding argument, not a formal
polynomial specialization or an approximation treated as equality.

Public APIs include `square_bounds`, `mark_sum_eq`, and `pair_matching`.

## Cardinality, height, and individual Sidonness

Different blocks are disjoint, even without assuming the marks are Sidon.
Their square-value sets are disjoint too. Consequently

    |union values(a)| = |A|*(H+1).

Every root is positive and at most 65 L(H+1). The module proves actual
containment of the union in the first 65 L(H+1) positive squares.

When H<=L, each FULL block is individually square-Sidon by the previously
proved short-interval criterion. APIs: `union_card`, `union_subset_squares`,
and `block_sidon`.

## Exact compatibility requirement remains

For arbitrary selected value sets V_a subset values(a), with H<=L,
`partial_union_sidon_iff` proves

    union V_a is Sidon
      iff the actual positive-difference sets of distinct V_a are disjoint.

`full_union_sidon_iff` specializes to all full blocks. `partial_union_card`
proves exact cardinality for arbitrary selected sets. `selected_lower`
transfers a COMPATIBLE selected family to the actual maximum at height
65 L(H+1), with lower bound sum_a |V_a|.

The compatibility hypothesis in `selected_lower` is explicit and UNPROVED
for any family useful to the original asymptotic conjecture. It is not
supplied merely by individual Sidonness or by the matching of block labels.

## Scope

The new construction supplies coarse pair separation without demanding
modular label matching. It does not dispose of collisions within two matched
blocks, supply a near-linear compatible partial family, or improve an actual
exponent for the original maximum. It is not an unrestricted upper bound.

The main file was not enlarged with this conditional construction and has
SHA-256 257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
