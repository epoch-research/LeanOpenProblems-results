# Controlled collision linearization

This is NOT a settlement of Erdős 773. Spec.lean is unchanged with its sole
admission for 0<epsilon<=1/3. No actual Sidon exponent improved.

## Four new audited modules

* PenalizedAlteration.lean
* ControlledSquareLinearization.lean
* HypergraphDegreeTrim.lean
* ControlledSquareDegrees.lean

All have clean builds and built .olean files. Their printed axiom audits use
only propext, Classical.choice and Quot.sound. None imports admitted Spec.

## Penalized alteration

`PenalizedAlteration.alteration` and `.ambient` add a nonnegative retained-edge
penalty mu to the Bernoulli objective. For forbidden supports H and a second
edge family G, the selected B avoids H and satisfies

    p|A| - sum_{e in H} p^|e| - mu sum_{e in G} p^|e|
      <= |B| - mu |{e in G : e subset B}|.

Deleting forbidden supports cannot increase the surviving G-edge count;
mu>=0 is explicitly assumed and used. Subtype transport supplies the version
for arbitrary finite ambient A, including exact transport of surviving edges.

`PenalizedAlteration.linearize` applies this to the six-vertex unions of
four-uniform edges overlapping twice. Under the preceding intersection and
pair-codegree hypotheses it gives linear surviving H and

    p|A| - p^6 |A|^2 K^2 - mu p^4 |H|
      <= |B| - mu |H restricted to B|.

## Square specialization

`ControlledSquareLinearization.edges_restrict` identifies the restricted
edge family with edges(B). `edges_card_le` covers all edges by two-root
fibers to give the coarse estimate |edges([1,N])| <= N^2 K when every pair
codegree is at most K. It intentionally does not claim a sharp constant.

The finite square theorem, starting with AP-free square values in roots
A subset [1,N], gives linear collision supports and

    p|A| - p^6 N^2 K^2 - mu p^4 N^2 K
      <= |B| - mu |edges(B)|.

`controlled_four_fifths` proves that for every epsilon>0, eventually an
actual AP-free, linear-collision root set B subset [1,N] satisfies

    N^(4/5-epsilon) + N^(-2/5-epsilon) |edges(B)| <= |B|.

The explicit parameters are

    |A| >= N^(1-epsilon/4),
    p = N^(-1/5-epsilon/4),
    K = N^(epsilon/8),
    mu = N^(-2/5-epsilon),
    S = N^(4/5-epsilon/2).

The two penalty terms equal respectively

    S*N^(-3epsilon/4),  S*N^(-11epsilon/8).

Each is eventually <=S/4; the target N^(4/5-epsilon) is eventually <=S/2.
The consequence `average_edge_control` supplies simultaneously

    |B| >= N^(4/5-epsilon),
    |edges(B)| <= N^(2/5+epsilon) |B|.

This explicitly controls the edges left after linearization. Cardinality
alone from the earlier linearization theorem would not have supplied this.

## Maximum-degree control

`HypergraphDegreeTrim.degree_sum` proves the incidence identity

    sum_{a in A} degree_H(a) = 4|H|

for a four-uniform H contained in A. `trim` shows that if |H|<=K|A| with
K>0, at least half the vertices have original incidence degree at most 8K.
Restricting the hypergraph only decreases these degrees.

`ControlledSquareDegrees.controlled_maximum_degree` combines this with the
controlled selection, using epsilon/4 and absorbing the factors 2 and 8.
For every epsilon>0, eventually an actual B subset [1,N] has

    |B| >= N^(4/5-epsilon),
    ThreeAPFree(B^2),
    linear four-root collision supports,
    maximum collision incidence degree <= N^(2/5+epsilon).

## Scope

This is still a RELAXED selection statement, not Sidonness. The maximum
degree remains polynomial. The ordinary four-uniform independent-set bound
has scale |B|/D^(1/3); substituting the main exponents gives

    4/5 - (2/5)/3 = 2/3.

Thus these results do not improve the actual main-gap exponent. A logarithmic
improvement from a stronger sparse-hypergraph theorem would also not by
itself prove any fixed epsilon<1/3. No such stronger independence theorem
was assumed, and none was formalized in this continuation.

There remains no near-linear square-specific rounding/selection theorem,
no actual exponent beyond 2/3-o(1), and no fixed-power upper bound disproving
the conjecture. No original proof or disproof was submitted.

## Logs

    /tmp/penalized-alteration.log
    /tmp/controlled-square-linearization.log
    /tmp/hypergraph-degree-trim.log
    /tmp/controlled-square-degrees.log
