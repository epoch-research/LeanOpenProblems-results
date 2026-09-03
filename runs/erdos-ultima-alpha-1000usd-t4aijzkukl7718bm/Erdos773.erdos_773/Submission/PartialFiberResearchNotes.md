# Partial residue fibers: exact compatibility and selection

This is NOT a settlement of Erdős 773. No improved actual main-gap exponent
or fixed-power upper bound was obtained. Spec.lean is unchanged, with its
sole admission for 0<epsilon<=1/3. No proof submission was made.

## Exact characterization for partial fibers

`PartialResidueFibers.lean`, namespace `Erdos773.PartialResidueFibers`, defines
`positiveDiffs A` to be the positive differences present in a finite set A of
VALUES. The verified `endpoints_unique` says a positive difference in a Sidon
set has a unique increasing pair of endpoints.

Let R be a finite set of residue labels and V_r arbitrary finite value sets,
all of whose members are congruent to r^2 modulo q. Assume the previously
defined `PairMatching q R`: square-sum residues identify unordered label pairs.
Then `sidon_iff_compatible` proves the EXACT equivalence

    union_r V_r is Sidon
      iff every V_r is Sidon AND the positiveDiffs V_r are pairwise disjoint.

This is not merely a sufficient full-fiber criterion. There is NO assumption
on index intervals, unit residues, or short-product injectivity.

`partial_square_iff` specializes to arbitrary index sets B_r and

    V_r = fiberValues q r B_r = {(q*k+r)^2 : k in B_r}.

`partial_card` proves, for q>0, that the union's cardinality is exactly
sum_r |B_r|. PairMatching prevents value overlaps between distinct labels.
`union_threeAPFree` proves that, when the individual fibers are Sidon, the
union contains no nontrivial three-term arithmetic progression. Indeed a
three-entry relation must, by PairMatching, lie in a single fiber.

## Strictly weaker than short-product injectivity

`sparse_two_fiber_example` proves that for EVERY q>=9 and H>0, the square
values from R={1,2}, B_1=B_2={0,H} form a Sidon set. These are four roots

    1, 2, q*H+1, q*H+2.

H is arbitrarily large relative to q, so the full-fiber length bounds cannot
be applied to these sparse fibers. `positiveDiffs_fiber_pair` verifies that
the two actual fiber differences are

    q*H*(q*H+2), q*H*(q*H+4),

which are distinct. Taking H=q*t makes BOTH selected short products
2*1*H and 2*2*H vanish modulo q (`short_product_alias`), despite compatibility.
Thus even short-product separation on the SELECTED index gaps is unnecessary.
This example has only four roots; it is not a near-linear construction.

## Verified overlap-cost selection

`PartialFiberSelection.lean`, namespace `Erdos773.PartialFiberSelection`,
retains the same residue hypotheses and assumes each V_r is Sidon. It defines

    E = |crossKeys R V|
      = sum_{r,s in R, r<s} |positiveDiffs(V_r) intersect positiveDiffs(V_s)|.

The ordering r<s counts each unordered label pair ONCE; no factor two is
hidden. `diffRep` chooses the increasing endpoints of a present difference.
Their uniqueness makes (r,s,D) determine a four-value support.

`obstruction_card_bound` proves that the actual number of Sidon obstruction
supports in U=union_r V_r is at most E. The proof checks all nontrivial
collisions, aligns labels using PairMatching, and identifies the appropriate
positive difference. Supports are mapped injectively from the subtype U to
ordinary natural-value finsets before the cardinality comparison.

`alteration` proves, for 0<=p<=1,

    maxSidonSubsetCard U >= p*|U| - p^4*E.

There is NO factor-four weak-Sidon extraction loss: union_threeAPFree makes
every obstruction have exactly four distinct vertices. All three-entry
obstructions are thereby accounted for, rather than omitted.

`partial_square_alteration` specializes this to the actual affine-square
fibers and uses the exact size sum_r |B_r|. `crossKeys_card` exposes the
finite intersection sum above.

## Remaining mathematical gap

No family with near-linear total size and sufficiently small E has been
constructed. In particular, a bound on the number of modular short-product
aliases is not itself a bound on E, and bounded difference capacity greater
than one does not provide a compatible root selector. The previous full-fiber
ceilings also cannot be transferred to arbitrary selected partial fibers.

A sufficient target remains: for every small delta>0, choose actual fibers
inside the squares up to root height N, with total size at least N^(1-delta)
and overlap cost E at most N^(1+delta). The new finite estimate would then
finish through the same exponent accounting as the low-collision reduction.
Neither this target nor the original conjecture has been proved.

## Verification

Both modules compile without admissions or warnings. All nine printed axiom
audits use only propext, Classical.choice, Quot.sound. Logs:

    /tmp/partial-residue-final.log
    /tmp/partial-fiber-selection-final.log

The new modules do not import the admitted Spec theorem. The original file
was checked again in /tmp/spec-partial-fiber-check.log and remains unchanged.
