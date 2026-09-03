# Fixed rough factor count — verified partial refinement

The conjecture in `Submission/Spec.lean` is still unresolved. Its original
statement, import, and `sorry` have not been changed. No complete proof or
irrational counterexample has been obtained or submitted.

## New verified file

`Submission/FixedRoughFactorCount.lean`
Namespace: `Erdos972FixedRoughFactorCount`.

Principal results:

* `exists_rough_almostPrime_beyond`: for irrational alpha>1 and arbitrary
  input threshold B and roughness threshold Z, there is a prime p>B whose
  output floor(alpha*p) is coprime to Z! and has at most 6144 prime factors,
  counted with multiplicity. Both thresholds are handled at one actual
  scale of `FourthPowerAlmostPrime.exists_prime_rough_log_scale`.
* `exists_fixed_rough_factor_count`: one fixed integer k, 1<=k<=6144,
  works simultaneously for EVERY pair B,Z: there is such a prime input
  with output factor-list length EXACTLY k. This uses finite pigeonholing
  over the frequently occurring counts, not separate choices of k for
  separate thresholds.
* `fixed_composite_count_of_finite`: if the original prime-pair set is
  finite, the fixed count can be taken with 2<=k<=6144. For every B,Z,
  some prime p>B then has exactly k output factors and every prime divisor
  of its output exceeds Z.

Also verified: `prime_iff_factor_length_one` and
`prime_factor_gt_of_coprime_factorial`.

## Scope and remaining gap

The result does not force k=1, does not eliminate k>=2, and is not a
counterexample. It retains multiplicities; it does not claim the output
is squarefree or has k distinct prime factors. It also does not remove
proper prime-power outputs.

It gives a fixed-count form of the existing almost-prime result, not a new
prime-correlation lower bound. An argument reducing the factor count while
preserving the same prescribed slope remains missing. Dividing by an
output factor changes the slope, and the rough witnesses have no bounded
output prime factor along a sequence with Z tending to infinity.

The fixed-parameter smoothing formulas were reviewed again. Their limits
remain compatible with finite prime pairs. No moving-parameter uniformity
or contradiction was obtained from this review.

## Verification

Command:

    lake env lean -o .lake/build/lib/lean/Submission/FixedRoughFactorCount.olean Submission/FixedRoughFactorCount.lean

The file compiles. The three principal printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
