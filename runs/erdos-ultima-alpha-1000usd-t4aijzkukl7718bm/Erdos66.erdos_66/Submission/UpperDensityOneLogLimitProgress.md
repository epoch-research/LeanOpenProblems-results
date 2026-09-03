# Uniform envelopes for the fixed-coefficient density-one construction

## Main conjecture status

The conjecture is still unproved and undisproved. Spec.lean is unchanged
with its original sorry. No proof submission has been made.

## Completed positive results

The potential selection has been factored into
`Erdos66HarmonicExceptionalProfile.exists_summable_potentials`. All earlier
exceptional-set results retain their statements and still compile.

`PotentialPointwiseEnvelopeExplore.lean` proves that the same set A can have
harmonically summable bad targets at every fixed tolerance AND, for each
fixed j, the eventual envelope

    |r_A(n)/log n-c| <= c/(j+1)+32(j+1).

This is a family of constant-width envelopes, not an error tending to zero.
At fixed c their right sides do not approach zero as j increases.

`UpperDensityOneLogLimitExplore.lean` proves:

* `exists_globally_bounded_log_limit_off_exception`: for every c>0 there
  exist A,E,K with K>=0, harmonic summability and natural density zero of E,
  convergence r_A(n)/log n -> c outside E, and for EVERY n,

      r_A(n) <= K+(2c+32) log(n+2).

* `exists_two_sided_log_limit_off_exception`: for every c>128 there exist
  A,E with the same exceptional-set and convergence properties and, eventually,

      (c/2-64) log n <= r_A(n) <= (3c/2+64) log n.

  In particular the lower coefficient is positive. This strengthens the
  previous construction at the exceptional targets but does not remove them.

## Proof and verification

Summability of a fixed nonnegative potential implies it is eventually below
one. Each exponential term is then at most n+2; taking logarithms bounds
both sides of r_A(n)-c log n. The elementary inequality
log(n+2)<=2 log n for n>=2 gives the displayed constants. A finite-prefix
bound r_A(n)<=n+1 supplies the global constant K.

All new production files compile and have built oleans.
`UpperDensityOneAxiomCheck.lean` audits the main results using only propext,
Classical.choice, and Quot.sound. The previously checked exceptional-set
results were recompiled and audited after refactoring.

## Exact remaining gap

The construction now supplies the global O(log n) bound required by the
repair machinery. It does NOT supply the sharper all-target asymptotic upper
bound r_A(n)<=(c+o(1))log n, nor summability of the actual deficits with weight
sqrt(log(n+2))/sqrt(n+1). Harmonic summability cannot by itself justify this
stronger weight: for example, the squares have a convergent reciprocal sum
but a divergent reciprocal-square-root sum. This comparison is not a claim
that the constructed exceptional set is the squares or has divergent repair
cost; the required cost is simply unproved.

Reviews of jittering, thinning, and local clipping supplied no rigorous
uniform-error improvement to a fixed coefficient. In particular, independent
small perturbations do not automatically remove the original exceptional
fluctuations, and no efficient simultaneous correction of the denser small-
tolerance exceptions has been established.
