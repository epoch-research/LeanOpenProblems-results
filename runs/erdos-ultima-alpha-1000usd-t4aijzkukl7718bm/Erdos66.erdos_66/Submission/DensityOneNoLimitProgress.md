# Harmonic exceptional control does not imply a pointwise limit

`PrescribedLogSpikesExplore.lean` and `DensityOneNoLimitExplore.lean` compile.
The principal result is
`Erdos66DensityOneNoLimit.exists_density_one_but_no_limit`.

It constructs a set B, an exceptional set E, and nonnegative constants K,C
such that:

- r_B(n) <= K+C log(n+2) at every n;
- sum_{n in E} 1/(n+2) converges;
- E has natural density zero;
- the function equal to 1 on E and r_B(n)/log n elsewhere tends to 1;
- r_B(n)/log n does not tend to any finite real constant.

The construction starts with the checked coefficient-1 density-one set.
At centers (k+1)^4 it adds ceil(log(center+2)) disjoint representation
packets using the existing multiplicity matching theorem. Their actual
weighted repair cost is summable by superquadratic separation. The intended
spikes force the normalized count to be at least 2 along the centers;
unintended changes are uniformly o(log n). The centers themselves have
summable reciprocal weight. Any hypothetical full limit must equal the
masked limit 1, since the complement of a harmonically summable set occurs
frequently. The spikes contradict that limit.

Scope: this disproves sufficiency of these auxiliary conditions, NOT the
existential conjecture in Spec.lean. It does not say every candidate must
have spikes. It does not strengthen the known universal fluctuation bound.
The original conjecture and its sorry remain unchanged.

`DensityOneNoLimitAxiomCheck.lean` audits the two main theorems.

## Strengthening: polynomially sparse exceptions at each fixed tolerance

`PowerExceptionsNoLimitExplore.lean` adds
`Erdos66PowerExceptionsNoLimit.exists_power_exceptions_but_no_limit`.
The SAME B can satisfy all the properties above and also, for every fixed
epsilon>0, have some 0<alpha<1 with

    sum_{|r_B(n)/log n-1| >= epsilon} (n+2)^(-1+alpha) < infinity,
    count(bad_epsilon,N)/(N+2)^(1-alpha) -> 0.

Start with the stronger power-saving base, not just the harmonic base.
Off the fourth-power centers, the normalized change is uniformly o(1).
Thus the new bad-epsilon set is eventually contained in the union of the
old bad-(epsilon/2) set and the centers. Replace the old exponent beta by
alpha=min(beta,1/2); the centers have a summable weight at this exponent,
by comparison with sum_k 1/(k+1)^2. A finite prefix does not affect
summability. The generic reciprocal-scale counting theorem supplies the
count bound. The no-limit argument is unchanged.

The power saving still depends on epsilon. This construction does not
claim the exact numerical envelopes of the earlier potential theorem,
only a global K+C log(n+2) bound with finite constants. It proves that even
the stronger combination of these qualitative upper and exceptional-count
properties is insufficient for a pointwise limit.

The new file compiles; `PowerExceptionsNoLimitAxiomCheck.lean` audits the
principal results using only propext, Classical.choice, Quot.sound.
