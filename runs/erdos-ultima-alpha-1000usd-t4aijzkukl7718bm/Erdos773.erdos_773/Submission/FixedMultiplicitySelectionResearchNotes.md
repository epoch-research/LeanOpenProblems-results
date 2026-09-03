# Quantitative selection for each fixed positive-difference capacity

This is NOT a settlement of Erdos 773. The original theorem requires capacity
ONE and exponent 1-o(1). At capacity one the new result only gives the existing
2/3-o(1) exponent. Spec.lean has not been changed.

## Verified theorem

`FixedMultiplicitySelection.lean`, namespace
`Erdos773.FixedMultiplicitySelection`, proves `fixed_multiplicity`:

For every natural g >= 1 and real epsilon > 0, eventually there is an actual
root set A subset [1,N] such that

    |A| >= N^(1 - 1/(2g+1) - epsilon),

and every positive square difference has at most g representations on A.
The exponent equals 2g/(2g+1)-epsilon. In particular g=2 gives
4/5-epsilon, whereas g=1 gives only 2/3-epsilon.

The theorem `finite_selection` is public as well. For an AP-free set of square
values coming from roots A subset [1,N], and a uniform representation bound K,
it produces C subset A with the required capacity and

    |C| >= p |A| - N^2 K^(g+1) p^(2g+2)

for 0 <= p <= 1. This finite theorem also permits g=0; the positive exponent
assertion uses g>=1.

## Why the support size improves

Work on the subtype of a finite root set A whose squared image is ThreeAPFree.
For any fixed positive difference, first endpoints are injective, as are last
endpoints. Moreover, their images are disjoint: if (a,b) and (c,a) are two
representations, then c^2+b^2=2a^2, contradicting AP-freeness and the strict
ordering in a representation. Consequently k representations use exactly 2k
roots.

Forbid the supports of all g+1 representations of a common difference.
Every such support has 2g+2 vertices. There are at most

    sum_{D=1}^{N^2} r_D^(g+1) <= N^2 K^(g+1)

supports. Bernoulli alteration on the subtype of A proves the finite bound.
The transfer back to natural roots checks an exact image equality for the
filtered representation sets and includes D>N^2, for which no pairs exist.

## Asymptotic parameters

Use the verified AP-free extraction to get |A|>=N^(1-epsilon/4).
The divisor representation bound gives K=N^(epsilon/4) eventually. Put

    q = 1/(2g+1),
    p = N^(-q-epsilon/2),
    S = N^(1-q-3epsilon/4),
    rho = 3g epsilon/4 > 0.

Then p|A|>=S and the deletion cost is exactly S*N^(-rho). The desired lower
bound is S*N^(-epsilon/4). Both factors eventually are at most 1/2, completing
the estimate without a leftover constant factor.

## Verification and scope

Compilation log: `/tmp/fixed-multiplicity-selection.log`.
Build: `.lake/build/lib/lean/Submission/FixedMultiplicitySelection.olean`.
Both public theorem audits report exactly

    propext, Classical.choice, Quot.sound.

There are no admissions, extra axioms, or compilation warnings. Dependencies
are Hypergraph, FractionalSquareSidon, and APFreeExtraction; none imports the
admitted Spec theorem.

This result quantitatively sharpens the earlier bounded-capacity selection,
not the actual Sidon lower bound. There is still no verified near-linear
conversion from g>1 to g=1, and no fixed-power upper bound disproving the
conjecture. No proof submission has been made.
