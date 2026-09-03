# Slice-preserving extension and the literal-radix obstruction

## Task status

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged and still contains its original `sorry`. No proof or disproof of
the existential natural-number statement has been obtained or submitted.

## Completed fixed-first selection

`FixedFirstSharedSelectionExplore.lean`, namespace
`Erdos66FixedFirstSharedSelection`, proves:

* `exists_extension_low_energy`: for q prime, h>0, 4h<q, and ANY prescribed
  integer label sequence f with |f_i|<=1, one admissible translate b has
  both the new character energy and the f-weighted new character energy
  at most 16h^2.
* `exists_fixed_first_root_flat`: holds an old translate a fixed. If its
  energy is at most C h^2, with C>=16, the second translate can be selected
  so that every shared root count has squared error at most 18C h^3.

This removes the need to reselect the old character sequence.

## Completed anchored repair

`AnchoredProductRepairExplore.lean`, namespace
`Erdos66AnchoredProductRepair`, uses

    anchoredSet h u v D = sharedSet h u v union (D x {0}).

Principal results:

* `pairCount_slice`: a general counting bijection when new coordinates
  can cancel only in the old slice.
* `anchoredSet_slice`: the new-zero coordinate slice is exactly the old
  parabola union, with exactly its old repair D.
* `anchoredSet_preserves_counts`: every representation count on that
  coordinate slice is exactly the old repaired representation count.
* `anchored_repair_bound`: assuming D is symmetric, disjoint from the old
  parabola union, and contained in two auxiliary parabolas, adding D x {0}
  costs at most 8h+8 at every nonzero product target.

The repair has no injective new-coordinate projection. That is not a gap
in this result: when the old target is zero, symmetry and disjointness
force the mixed repair count to vanish. Otherwise the old projection
provides the existing bound.

## Actual slice-preserving finite flat extension

`SlicePreservingFlatExtensionExplore.lean`, namespace
`Erdos66SlicePreservingFlatExtension`, proves
`exists_slice_preserving_flat_extension`.

Given an admissible old translated parameter interval with energy <=24h^2,
and a fixed old auxiliary repair with T.card=floor(h^2/2), there is a set
in the product of the old and new planes such that:

1. Its old-coordinate slice is exactly the prescribed old repaired set.
2. Every count on this slice is exactly preserved.
3. At EVERY product-group target, including the origin,

       (pairCount(A,A;z)-h^2)^2 <= 1512 h^3.

The new prime need only satisfy q>4h. It need not exceed h^2/2 because the
repair remains entirely in the old plane. The old field must accommodate
the specified interval and repair, as stated in the theorem's hypotheses.

This extends one field plane by one new field plane at FIXED h. It is not
an arbitrary-number-of-factors extension, a growing-mean extension, or an
integer-prefix extension.

## Checked obstruction: product cubes

`SharedProductCubeExplore.lean`, namespace `Erdos66SharedProductCube`:

* `pairCount_pi`: exact multiplicativity for finite Cartesian products.
* `cube_peak`: a product of k nontrivial two-point sets forces at least
  2^k representations of its coordinatewise center in every containing set.
* `product_curve_peak`: a product of k parabola curves contains such a
  cube, using the two points (0,0) and (1,1/u_i) in each factor.

Thus adding labels or repairs cannot remove this exponential peak. A
fixed-h shared-label construction cannot remain uniformly bounded through
arbitrarily many factors. This is a statement about the construction, not
an obstruction to arbitrary natural-number sets.

## Checked obstruction: literal mixed-radix gaps

`SharedProductRadixGapExplore.lean`, namespace
`Erdos66SharedProductRadixGap`, analyzes the literal encoding

    e(old) + M * (new_x.val + q * new_y.val),

where every old code is below M.

A nonzero-parameter parabola meets new_y=0 only at the new origin.
Consequently, for an anchored shared set, every encoded element below Mq
is already below M. This gives the exact theorem
`anchored_encoding_hole`:

    sumRep(encoded anchored set, n) = 0   for 2M <= n < Mq.

`prefix_gaps_exclude_nonzero_limit` proves that ANY natural set with these
prefix gaps for unbounded old lengths and q>=3 cannot have the conjectured
nonzero limit. Thus the literal mixed-radix iteration of these exact
slice-preserving templates is ruled out, not merely unproved.

The gap theorem does NOT apply to arbitrary nonlinear reorderings, shifted
curves, or arbitrary natural-number sets; none is claimed to solve the task.

## Verification

All five new development files compile and have built oleans.
`SliceCompatibilityAxiomCheck.lean` and
`SharedProductObstructionAxiomCheck.lean` audit the principal theorems.
Only propext, Classical.choice, and Quot.sound occur.

## Remaining mathematical gap

The two optional finite compatibility steps from
`SharedParameterSetProgress.md` are now complete. The literal radix
realization nevertheless has the proved gap above, and repeated Cartesian
factors have the proved cube peak. Further finite flatness alone does not
supply the missing inhomogeneous, compatible natural-number construction.
A valid submission still requires a genuine solution of that infinite
problem, or a universal contradiction not restricted to these constructions.
