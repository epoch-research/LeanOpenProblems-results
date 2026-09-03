# Shared-parameter product sets: multiplicity removed and origin repaired

## Original task status

The original conjecture is still unresolved. `Spec.lean` is unchanged with
its original `sorry`. No valid proof or disproof has been submitted.

## Completed finite construction

`SharedParameterFlatSetExplore.lean` now proves
`Erdos66SharedParameterFlatSet.exists_shared_flat_set`:

For primes p,q and h>0 satisfying

    max(8h, floor(h^2/2)) < p,q,

there is an ACTUAL finite set

    A subset (ZMod p)^2 x (ZMod q)^2

such that, at EVERY product-group target z,

    (pairCount(A,A;z) - h^2)^2 <= 1512 h^3.

This includes the origin. The relative error tends to zero as h grows.
The mean remains h^2, not h^4 as in an independent Cartesian product.

## Checked pipeline

* `CommonOriginFamilyExplore.lean`: exact generic convolution correction
  for a finite family whose members meet only at zero. The union indicator
  differs from the sum of member indicators by (number of labels - 1)
  times the point mass at zero.

* `SharedParameterSetExplore.lean`: product parabolas with injective,
  nonzero parameter labels meet only at the global origin. It proves the
  exact correction to the previously checked weighted root count; at
  nonzero targets its magnitude is at most 2h. The unrepaired set has
  representation count exactly 1 at the origin.

* `ProductProjectionRepairExplore.lean`: a symmetric disjoint repair D
  with injective projections to each field plane has mixed count at most
  4h and self-count at most 8 at every nonzero product target, provided its
  projections lie on two suitable auxiliary parabolas. Its origin count
  is exactly |D|. Thus its collateral contribution is at most 8h+8.

* `AlignedProductRepairExplore.lean`: constructs such a repair with exactly
  2m points for any m<p,q. It pairs signed partial-parabola points using
  the SAME index in both fields. Both projections are injective. Parameters
  outside the old parameter sets and their negatives ensure disjointness.

* `SharedParameterFlatSetExplore.lean`: chooses m=floor(h^2/2). The repaired
  origin count is h^2 or h^2+1. At nonzero targets the weighted error plus
  2h+8h+8 gives the displayed squared-error bound.

All files compile and have built oleans. `SharedParameterSetAxiomCheck.lean`
audits the principal results; only `propext`, `Classical.choice`, and
`Quot.sound` occur.

## Remaining limitations

The ambient group is the PRODUCT of two finite-field planes. This is not
an integer mixed-count theorem for patterns of different periods. No
intermediate-scale or infinite-prefix result follows from it automatically.

For k factors, a naive shared-label expansion involves all nonempty subsets
of the k character sequences. The current bound has exponential dependence
on k. Reusing the very same character sequence in multiple factors is not
an automatic cure: products of repeated sign sequences can become the
constant sequence, which has large additive energy.

## Update: both finite compatibility steps are now checked

See `SliceCompatibilityProgress.md`. Fixed-first selection and the anchored
repair now give an actual slice-preserving finite flat extension. The same
review also proves a literal mixed-radix gap and a product-cube peak; neither
finite compatibility result settles the original natural-number conjecture.

## Earlier proof plan (now completed; retained for context)

An anchored repair supported on the old plane times {0}, instead of the
aligned repair used above, may preserve an old repaired template exactly
as a coordinate slice. If the old target component is nonzero, its injective
old-plane projection supplies the existing bound. If the old target is
zero but the new target is nonzero, unused-parameter disjointness may force
the mixed count to vanish. This would require a separate proof.

Likewise, the weighted indexed-energy average can be used to select the
second field's translate while holding the first translate fixed, if the
first sign sequence already has small energy. The joint-selection theorem
currently in the pipeline does not assert this stronger compatibility.

Even proving both finite observations would only preserve a GROUP slice.
A mixed-radix realization still has integer carries and a nontrivial
inhomogeneous density profile at intermediate scales. These remain genuine
missing steps for the original conjecture.
