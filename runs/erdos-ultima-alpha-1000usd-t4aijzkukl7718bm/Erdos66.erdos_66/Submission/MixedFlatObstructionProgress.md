# Self-flatness does not control mixed counts

The original conjecture remains unresolved; `Spec.lean` is unchanged.

`MixedFlatObstructionExplore.lean` now compiles. Its main theorem,
`Erdos66MixedFlatObstruction.exists_unbounded_mixed_peak`, states:

For every eta>0 there is beta>0 such that for every R>0 there are a finite
cyclic group and two sets B,C with both self-convolutions uniformly within
eta*beta of beta, but their mixed convolution at zero exceeds R*beta.

The construction is C=-B, using the existing arbitrarily large-period flat
cyclic family. Reflection preserves self-flatness. The mixed count at zero
is exactly |B|, while summing the self-count lower bound forces
|B|^2 >= M*(1-rho)*beta, with rho=min(eta,1/2). Thus |B|/beta is unbounded as
the period M grows, although beta is fixed before M.

`MixedFlatObstructionAxiomCheck.lean` confirms only propext, Classical.choice,
and Quot.sound are used.

This is NOT a disproof of the existential natural-number conjecture. It rules
out an inference that might otherwise be used incorrectly to glue separately
self-flat templates. Existing controlled mixed families use a common period;
no comparable theorem across a change of period has been established.

Lean note: the generic Finset reflection lemmas need an explicit
[DecidableEq G] parameter. Otherwise their synthesized classical equality
instance can prevent rewriting a concrete ZMod Finset.image expression.
