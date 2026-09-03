# Review of multiscale amplification

## Status

The original conjecture is still unproved and undisproved. Spec.lean is
unchanged. No new theorem resolving it and no valid proof submission have
been obtained in this pass.

## Analytic route checked

The sharp fluctuation theorem removes the factor-two loss in the radial
comparison by applying weighted convolution-square stability at different
geometric tilts. Its checked consequence is a necessary squared-error
coefficient at least c on the log(n) scale.

A possible further step was to combine comparisons at many radii, or let
the tilt increase with the radius. No logarithmic-order amplification was
obtained. If N denotes the effective cutoff after tilting, the squared-mass
term still has order N log N. The conjectural pointwise error o(log n)
is compatible with squared-error mass o(N log^2 N).

The distinction is essential. A relative error envelope tending to zero
need not have its square times log N tend to zero. For example the scalar
rate (log N)^(-1/4) tends to zero, but its square times log N tends to
infinity. This example is only a rate comparison, not a representation
function or a witness to the conjecture.

Nonnegative averaging of the comparisons currently available has not
removed this gap. Allowing a variable tilt changes the effective scale;
it does not by itself supply the missing rate of convergence. No universal
impossibility theorem for other multiscale methods is claimed.

## Remaining alternatives

A resolution would still require either a genuinely stronger consequence
of the 0/1 convolution structure, or a compatible infinite construction.
The finite cyclic families and the rejected digit-walk candidate do not
provide either one.
