# Row geometry and prefix-independent annular extension

## Original task status

The original conjecture is unresolved. `Submission/Spec.lean` is unchanged
and still contains its original `sorry`. No proof or disproof has been
submitted.

## Checked gain

A horizontal row meets a nonzero-parameter parabola `y=x^2/u` in at most TWO
points. A repaired union of h main parabolas lies in h+2 such parabolas.
After coordinate thickening by K, each row of width pK has at most
2K(h+2) points. An arbitrary interval no longer than one row meets at most
two rows. Consequently, adjoining any disjoint prefix of length at most pK
changes representation counts beyond twice that length by at most
8K(h+2), regardless of the number of old points.

The row bound was proved for the actual existing block encoding, not only
for a newly defined model. It survives the tapered finite construction and
translation. With the tuned K on the sqrt(log p) scale, this mixed-count
bound divided by log p tends to zero.

## Main files and results

* `RowSparsePrefixExplore.lean`: `union_short_prefix_bound`.
* `GraphRowGeometryExplore.lean`: `repaired_graphRows_prefix_bound`.
* `GraphBlockGeometryExplore.lean`: `thickened_block_prefix_bound`.
* `GraphPrefixLimitExplore.lean`: `tuned_short_prefix_negligible`.
* `FlatRowFamilyExplore.lean`:
  `exists_mixed_flat_prime_family_with_rows`.
* `RowSparseShiftExplore.lean`: `rowSparse_shift`.
* `UniformRowFamilyExplore.lean`: `exists_uniform_row_family`.
* `ShiftedFiniteRowsExplore.lean`:
  `exists_shifted_finite_blocks_with_rows`.
* `RowControlledAnnulusExplore.lean`: `exists_row_controlled_annulus`.
* `UniformPrefixAnnulusExplore.lean`: `exists_uniform_prefix_annulus`.

The last theorem selects b, N, and a finite new set D FIRST. The SAME D
works for every old finite A contained in [0,b) and satisfying the global
upper envelope r_A(n)/log n <= c. It preserves that envelope, preserves
membership below b^2, and gives accuracy epsilon on [N,RN]. Here b>=N0,
b>=2, N>=b^2, and D is supported at or above b^2.

This is a genuine improvement in quantifier order over selecting a new
annulus after seeing the old prefix. It does not assert an upper bound on
the selected prime or on N as a function of b.

## Verification

All ten development files compile and have built oleans.
`RowGeometryAxiomCheck.lean` and `UniformPrefixAnnulusAxiomCheck.lean` audit
the principal results; only propext, Classical.choice, and Quot.sound occur.

## Remaining gap

The construction has a forced support gap: old points are <b, new points
are >=b^2. Thus all counts vanish for 2b<=n<b^2. It is not a compatible
infinite construction and does not provide a lower bound through a scale
transition. In particular, iterating this extension does not prove the
original limit.
