# Review of batched repair

## Status

The original conjecture remains neither proved nor disproved. `Spec.lean`
is unchanged and still contains its original `sorry`. No new solution or
proof submission is claimed in this review.

## Potential saving

Repairing a cluster of L targets, each requiring about m representations,
by separate symmetric packets costs on the order of mL points. A packet
whose self-sums cover the whole cluster could potentially use order
sqrt(mL) points. This is also the natural counting lower scale, since the
total number of ordered pairs from a packet F is |F|^2.

The finite constant-profile and mixed-template constructions suggest ways to
make localized profiles. They do not yet give a packet compatible with an
arbitrary existing base at the required asymptotic upper coefficient.

## Unresolved collateral

Two terms must be controlled, not just the desired representations:

1. Self-sums of the packet outside the target cluster.
2. Mixed sums between the packet and the pre-existing set.

A plateau in the self-convolution need not be supported only on that plateau.
For example, using two blocks to produce a constant mixed plateau also gives
two self-sum lobes. Treating those lobes as negligible is unjustified.

For randomized local profiles, shrinking relative error is available when
the logarithm of the local window size is small compared with the desired
mean. At mean c log N and window length N^delta, the current concentration
criterion still imposes a condition involving delta/(c epsilon^2). It does
not automatically allow epsilon to tend to zero for fixed delta>0.

Structured cyclic templates can avoid that particular finite concentration
loss, but their interaction with the existing integer set still needs a
separate mixed-count estimate. Same-period mixed flatness does not establish
that estimate across an arbitrary scale transition.

## Conclusion

No base with the necessary clustered-deficit structure and no compatible
batched-completion theorem sufficient for the original conjecture has been
obtained. No inference from these observations to a universal disproof is
valid.
