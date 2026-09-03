# Nonuniform partial-fiber selection

This continuation does **not** settle Erdős 773. `Spec.lean` is unchanged and
still has the one admission at line 2031 for 0 < epsilon <= 1/3.

## Verified nonuniform selection

`WeightedHypergraph.lean` generalizes the independent finite Bernoulli proof to
a probability for each vertex. Its Sidon alteration theorem is

    sum_{a in A} p(a) - sum_{e in sidonObstructions(A)} prod_{a in e} p(a)
      <= maxSidonSubsetCard(A).

All probabilities lie in [0,1]. The proof is finite expectation followed by
one-vertex-per-obstruction deletion; no measure-theoretic assumptions or
rounding conjecture are used.

`WeightedPartialFibers.lean` specializes this to individually Sidon value
fibers V_r with modular pair matching and the correct square residues:

    sum_r p_r |V_r|
      - sum_{r<s} p_r^2 p_s^2 |positiveDiffs(V_r) intersect positiveDiffs(V_s)|
      <= maxSidonSubsetCard(union_r V_r).

The support product has exactly two distinct vertices from each of two
*different*, disjoint fibers. The original `collision_key` lemma was made
public in `PartialFiberSelection.lean`; its proof was unchanged. The support
cover and nonnegative weighted sums handle possible repeated keys without
assuming key injectivity. The `partial_square_alteration` specialization uses
arbitrary index sets B_r and replaces |V_r| by |B_r|, with q>0.

## Threshold bounds

The same file defines T={r in R : t <= p_r}. For t>=0:

    sum_r p_r m_r - t sum_r m_r <= sum_{r in T} m_r,
    t^4 |crossKeys(T,V)| <= sum_{k in crossKeys(R,V)} p_{k.r}^2 p_{k.s}^2.

The first assumes p_r<=1, and m_r are natural sizes. The second needs no
modular or Sidon hypothesis. These are finite bounds, not a construction of a
favorable family. In particular, a near-linear weighted certificate at height
N with a useful cost would, by an appropriate small threshold, yield a
near-linear unweighted low-overlap family. No such family is currently known.

## A genuine finite square example

`WeightedSquareExample.lean` constructs roots for i=0,...,9:

    y_i = (3*19^(18-i) - 19^i)/2,
    x_i = (3*19^(18-i) + 19^i)/2.

All divisions are exact. Their squares differ by the same positive constant

    C = 3*19^18 = 312382050893733724598523.

The two value fibers each have ten values, are individually Sidon, and have
residues 1 and 4 modulo 9. Labels {1,2} satisfy PairMatching 9. There are exactly
45 common positive differences. These finite certificates use `decide
+kernel`, not `native_decide`.

For p_1=1 and p_2=1/9, the weighted lower bound is

    10 + 10/9 - 45/81 = 95/9.

For every p>=0, the *uniform expression* on this same union satisfies

    20p - 45p^4 <= 8.

The verified inequality follows from

    p^4 >= p/2 - 3/16,
    p^4 - p/2 + 3/16 = (p-1/2)^2 (p^2+p+3/4).

This is a ceiling on that expression, **not** an upper bound on the actual
Sidon maximum. In fact the actual maximum on this union is exactly 11:
integrality and the nonuniform certificate give the lower bound, and the
translated-union theorem below gives the upper bound.

The largest root is 156191025446866862299262. Thus this finite advantage is
not a near-linear root-height construction. No claim is made that this
20-value union is maximal among all square subsets at that height.

## Arithmetic limitation of translated fibers

`TranslatedSquareFibers.lean` proves, for any natural-value set A and C>0,

    maxSidonSubsetCard(A union (A+C)) <= |A|+1.

A Sidon subset can contain both a and a+C for at most one position a in A:
two such positions immediately give a nontrivial equal sum. Counting the two
copies then proves the bound; overlap of A and A+C is allowed.

It also defines `commonValues N C`, the square values a at root height N for
which a+C is also a square at root height N. These values inject into
`squareDifferenceReps N C`. Consequently, for every delta>0 there is K_delta
such that uniformly in N and C>0,

    |commonValues N C| <= K_delta N^delta.

The case C>N^2 is empty. `translated_fiber_subpower` applies this to any actual
square fiber whose positive translate also consists of squares at that
height. Hence the exact-translate mechanism producing the finite weighted
advantage cannot itself supply a near-linear family.

This does not bound arbitrary shared-difference patterns or arbitrary
nonuniform selections. Equal difference sets need not be translates, and
no such converse has been assumed.

## Verification

All four new files compile without warnings or admissions and have built
`.olean` files. Printed axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`.

Logs:

* /tmp/weighted-hypergraph.log
* /tmp/weighted-partial-fibers.log
* /tmp/weighted-square-example.log
* /tmp/translated-square-fibers.log

None of these modules imports the admitted `Spec.lean`; none has been
consolidated into it. No proof submission has been made.

Practical Lean note: avoid running broad `norm_num` on an inequality with
`maxSidonSubsetCard` of a concrete 20-element set on its other side. It can
start evaluating that finite maximum. Normalize the scalar left side in a
separate equality and rewrite it into the bound instead. The extensional
membership proof of the translate-image identity also avoided a deep kernel
recursion encountered in the direct `image_congr` proof.
