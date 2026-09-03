# Refining-measure and shrinking-window route: unchecked endpoint review

## Status

This is a mathematical review, not a Lean theorem. It supplies no proof or
disproof of the original conjecture. Submission/Spec.lean is unchanged with
its original sorry. No claimed external theorem was used.

## Proposed mechanism

One might try using shrinking neighborhoods of a singular measure on the
circle whose self-convolution has a continuous density. Averaging many
translated copies could smooth that density towards a constant. Applying
such windows along a rotation would then require uniform discrete pair-count
estimates at the shrinking scale, as well as the correct density at every
natural cutoff.

This differs from simply reading the Cantor tree as the set of natural
prefixes: the window is in an auxiliary phase coordinate. It nevertheless
has two unproved essential requirements:

1. a uniformly sparse support-neighborhood bound at EVERY resolution, not
   only at selected construction levels;
2. an all-target discrepancy estimate for the shrinking-window rotation,
   including correlations between the two summand windows.

Neither requirement follows from continuity of the measure's self-convolution.
No suitable measure or rotation with both properties was constructed.

## Intermediate-resolution issue

Products of finite sparse, flat templates may look promising at the selected
refinement moduli. A large new digit alphabet, however, introduces a long
interval of intermediate resolutions. If its selected digits are spread
through the new parent interval, their neighborhoods can cover most of that
interval before the individual digits are resolved. The number of occupied
cells can then grow essentially linearly through part of the refinement,
rather than with the square-root/logarithmic profile needed here.

Thus selected-level sparsity or Hausdorff-dimension information cannot be
substituted for a uniform support-neighborhood estimate. This is a limitation
of the proposed argument, not a proved impossibility for all refining measures.

## Other endpoint checks

An abstract bounded-representation basis in a group with negative elements
or a divisible additive structure does not transport to a positive natural
basis by an arbitrary enumeration. Such an enumeration need not preserve
sums. Squaring, taking absolute values, or using a changing radix also needs
a new representation-count theorem; none was obtained.

The existing finite natural annuli, exact-bracket restoration results, and
energy bounds still do not provide the missing all-scale estimate or a
universal logarithmic-size obstruction. No valid final proof is available.
