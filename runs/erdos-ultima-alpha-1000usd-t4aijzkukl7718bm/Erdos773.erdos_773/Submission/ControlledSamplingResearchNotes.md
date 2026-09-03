# Exact-cardinality and progression-free square sampling

This work does NOT settle Erdős 773. The main file remains unchanged, with
its sole admission for 0 < epsilon <= 1/3. No submission has been made.

## Exact finite averaging

`FixedCardinalitySampling.lean` proves weighted selection of exactly k
vertices from an ambient finset A of size n. For nonnegative edge weights,
one can choose B subset A with |B|=k and

    sum_{e subset B} W(e) <= sum_e W(e) (k/n)^|e|.

The proof inducts by deleting one vertex at a time. The survival factor is
bounded by Bernoulli's inequality, so no probability measure or fluctuation
in cardinality is needed. Empty edges and k=0 are covered. Two-family
weighted and simultaneous threshold versions are included. This is a
sampling bound, not an independent-set theorem.

## Progression supports

`SquareProgressionSupports.lean` defines the actual three-root supports
of square three-term progressions in A. It proves restriction/monotonicity,
the global bound by the earlier squareAPs family, and that avoiding these
supports gives a ThreeAPFree square-value image.

## Controlled logarithmic sampling

`ControlledSquareSampling.lean` combines the exact sampling theorem,
progression deletion, and the sharp unordered four-root count. For every
delta>0, eventually there is B subset [1,N] with square values ThreeAPFree,

    (1-delta) N/log N <= |B| <= N/log N,
    E4(B) <= (41/500+delta) N^2/(log N)^3.

The finite proof samples k=floor(N/log N) roots, controls both edge families
with a normalized weighted cost, and deletes at most the progression count.
This retains the fourth-order density saving in the four-edge count.

`sharp_carrier` specializes delta=1/2000 and combines the result with the
uniform subpower pair-codegree bound. For every gamma>0, eventually the same
B satisfies

    (1999/2000) N/log N <= |B| <= N/log N,
    E4(B) N^2 <= (83/1000) |B|^4 log N,
    every pair codegree <= N^gamma.

The normalized constant follows from the exact rational comparison

    33/400 <= (83/1000) (1999/2000)^4.

All three modules are built and their printed axiom audits use only
propext, Classical.choice, Quot.sound. Latest logs:

* /tmp/fixed-cardinality-sampling.log
* /tmp/square-progression-supports.log
* /tmp/controlled-square-sampling.log

## Remaining gap

B can still have many four-root collisions. None of these results asserts
Sidonness, a new Sidon exponent, a logarithmic-gain extraction theorem, or
the endpoint epsilon=1/3. Generic sparse-hypergraph methods, even if strong
enough to recover that endpoint, would leave 0<epsilon<1/3 unresolved.
