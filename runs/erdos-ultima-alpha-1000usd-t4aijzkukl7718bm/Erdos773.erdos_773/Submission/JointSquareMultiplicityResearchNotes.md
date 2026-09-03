# Actual square sets with simultaneous fixed capacities

The original Erdos 773 conjecture remains UNSETTLED. Spec.lean was not edited
and still contains its one admission. No original lower exponent above 2/3,
no fixed-power upper bound, and no complete proof or disproof was obtained.

## Completed module

Submission/JointSquareMultiplicity.lean imports only clean auxiliary modules,
not Spec.lean. It builds without warnings, errors, or admissions and has an
olean. All four printed axiom audits use only propext, Classical.choice,
and Quot.sound.

Namespace: Erdos773.JointSquareMultiplicity
Log: /tmp/joint-square-multiplicity.log

## Quantitative actual-square theorem

fixed_joint_multiplicity proves that for EVERY fixed integer g>=1 and every
epsilon>0, eventually there is C contained in the first N positive squares
with

    |C| >= N^(1 - 1/(2g+1) - epsilon),

such that C is three-term-progression-free and BOTH of the following hold:

* every positive difference has at most g increasing representations in C;
* every sum has at most g unordered representations in C, INCLUDING a
  possible diagonal representation.

The objects in C are square VALUES, not root indices. Containment in the
actual image of [1,N] under squaring is part of the theorem.

near_linear_joint_capacity proves the corresponding relaxed near-linear
statement: for every epsilon>0 there EXISTS a fixed g>=1 such that, for every
sufficiently large N, such a C has |C|>=N^(1-epsilon). It does NOT give this
near-linear bound for every fixed g, and in particular does not assert g=1.

## Finite certificate

For AP-free A contained in the first N squares, assume all square-difference
and square-sum representation counts at height N are at most K. For p in
[0,1], finite_selection produces C subset A with both capacities <=g and

    |C| >= p|A| - 3N^2 K^(g+1) p^(2g+2).

The generic indexed_selection handles any finite collection of pair families
whose subfamilies use exactly twice as many endpoints as pairs. It forbids
the endpoint supports of all g+1 representations in each family. Their total
count is at most |I| K^(g+1), and each support has exactly 2g+2 vertices.

For the square application, I consists of positive differences up to N^2
and positive sums up to 2N^2, so |I|=3N^2. AP-freeness makes equal-difference
pairs disjoint. Strict unordered representations of one sum are disjoint
without that extra hypothesis. The possible diagonal sum representation is
handled afterwards: AP-freeness means it cannot coexist with a strict one.

The square representation bounds are transferred to the value carrier by
the checked injective map (x,y) -> (sqrt(x),sqrt(y)). Its correctness uses
actual square membership. Out-of-range sums and differences have empty
representation sets and are explicitly included in the final capacities.

## Asymptotic parameters

Use an AP-free carrier of size at least N^(1-epsilon/4), and put

    q=1/(2g+1), p=N^(-q-epsilon/2), K=N^(epsilon/4),
    T=N^(1-q-3epsilon/4), rho=3g epsilon/4.

The leading mass is >=T. The cost is exactly 3T*N^(-rho), eventually <=T/2.
The target is T*N^(-epsilon/4), eventually <=T/2. The divisor estimates for
both sums and differences provide K eventually, with all constants absorbed.

## Scope and the remaining gap

This strengthens the previous difference-only actual-square selection by
simultaneously imposing the sum bound. At capacity one it STILL only yields
the two-thirds exponent. No square-specific subpower-loss conversion from
larger joint capacity to Sidonness has been proved.

The older ordinary-integer joint-capacity counterexamples remain relevant:
the two capacities and AP-freeness alone cannot justify a generic near-linear
rounding theorem. Conversely those examples are not asserted to be squares
and cannot be used as an upper bound for the original maximum.

No incomplete main proof has been submitted.
