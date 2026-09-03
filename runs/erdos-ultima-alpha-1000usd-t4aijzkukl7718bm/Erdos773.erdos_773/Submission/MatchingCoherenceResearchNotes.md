# A quantitative limitation of global matching-coherence codes

This does NOT settle Erdős 773. The conjecture in Spec.lean is unchanged,
with its one remaining admission for 0 < epsilon <= 1/3.

## Verified theorem

`MatchingCoherenceBound.lean` imports the previously verified generic
`SumsetIncidence` module. A code C is a finite subset of a product X*Y.
`Coherent C` requires that matching the two first-block entries of two
codeword pairs, and independently matching their two second-block entries,
forces one matching of the whole codeword pairs.

The file proves

    |C| <= |projection_Y C| sqrt(|projection_X C|) + |projection_X C|.

For finite available alphabets, it also proves

    |C| <= |Y| sqrt(|X|) + |X|.

When both alphabets have size R, the entirely integral consequence is

    |C|^4 <= 16 (R^2)^3.

Thus this criterion has a three-quarters ceiling relative to the size R^2
of the balanced Cartesian box. R=0 is included.

## Why the bound applies

The four corners (x,y), (x,z), (w,y), (w,z) would give two independent
blockwise pair matchings. Coherence forces x=w or y=z. Hence every distinct
pair of right vertices has at most one common left neighbor. The existing
two-path/Cauchy-Schwarz incidence inequality then yields the bound.

The incidence count is proved equal to the code's cardinality; the proof
does not count a codeword multiple times or rely on surjective projections.

## Individual-coordinate version

`CoordinateCoherent` makes the matching assumption separately for each
coordinate in two blocks. `coordinate_implies_block` verifies that this
implies block coherence for any such split. Consequently, for 2d coordinates
over an m-letter alphabet,

    |C| <= m^d sqrt(m^d) + m^d.

The bound applies regardless of how the code was chosen; no linearity or
minimum-distance hypothesis is used.

## Scope

This constrains a proposed way of reconciling the independently swappable
matchings supplied by local Sidon restrictions. It does NOT prove that
arbitrary Sidon subsets of integer squares satisfy this coherence criterion,
and does NOT identify the Cartesian-box size R^2 with the root height in
the original problem. In particular, it is not a fixed-power upper bound on
Finset.maxSidonSubsetCard of the first N squares. Constructions with weaker
local conditions, or a different global compatibility argument, are not
ruled out by the theorem.

No new actual Sidon lower exponent or disproof was obtained in this
continuation. The bounded-multiplicity conversion remains unproved too.

## Verification

The module builds without errors, warnings, admissions, or extra axioms.
All five printed audits use only propext, Classical.choice, Quot.sound
(the coordinate-to-block implication needs only propext and Quot.sound).

    /tmp/matching-coherence-bound.log

Built module: .lake/build/lib/lean/Submission/MatchingCoherenceBound.olean.
