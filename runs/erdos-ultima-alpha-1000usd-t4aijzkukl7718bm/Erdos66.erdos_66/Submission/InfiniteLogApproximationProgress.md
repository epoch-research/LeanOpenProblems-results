# Infinite fixed-relative-tolerance approximation

## Main conjecture status

The original theorem in `Submission/Spec.lean` is unchanged and unresolved.
The results below do not prove convergence at a single fixed coefficient.

## Completed positive infinite result

`InfiniteLogApproximationExplore.lean` proves:

* `Erdos66InfiniteLogApproximation.exists_with_coefficient`: for every
  `0 < delta <= 1`, there exists an infinite-set candidate A with

      eventually |r_A(n)/log n - 16/delta^2| <= 5 delta (16/delta^2).

* `exists_fixed_relative_log_approximation`: for every epsilon>0, there
  exist A subset N and c>0 such that

      eventually |r_A(n)/log n-c| <= epsilon c.

For epsilon<5 the construction takes c=400/epsilon^2. The coefficient
therefore increases without bound as the requested tolerance shrinks.
The theorem does not assert that A is infinite as part of its type, but
for any relative tolerance below one this follows from the positive lower
logarithmic representation envelope.

## Checked ingredients

* `ScaledFractionalTailExplore.lean` shifts and scales the exact fractional
  harmonic profile to obtain probability weights in [0,1] with convolution
  asymptotic to any prescribed c log n. A shift by S changes its convolution
  by at most 2S. The finite Bernoulli representation mean is between this
  convolution and the convolution plus one, uniformly in the final cutoff.
* `SummedBernoulliBoundsExplore.lean` sums the target-dependent Chernoff
  estimates rather than multiplying the largest estimate by the number
  of targets.
* `SummableTailBudgetExplore.lean` supplies one threshold controlling all
  finite tail sums of 2/(n+2)^4.
* `RepEnvelopeCompactnessExplore.lean` turns finite witnesses on [N,L]
  for every L, with N fixed first, into one infinite witness for that
  single envelope.

With V(n)=2c log(n+2) and c=16/delta^2, the summed failure estimate is
exactly 2 exp(-delta^2 V(n)/8)=2/(n+2)^4. The pointwise deviation costs at
most 4 delta c log n and the mean error costs at most delta c log n.

All files compile and have built oleans. `InfiniteLogApproximationAxiomCheck.lean`
audits the main results using only propext, Classical.choice, and Quot.sound.

## Exact limitation

Summing individual tails fixes the cutoff-uniformity issue for ONE fixed
tolerance. It does not remove the summability threshold on delta^2 c.
Taking delta to zero changes c; compactness does not interchange these
quantifiers. No main-conjecture proof or disproof is being claimed.
