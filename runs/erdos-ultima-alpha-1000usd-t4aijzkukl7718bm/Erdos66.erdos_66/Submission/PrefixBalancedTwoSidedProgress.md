# Prefix-preserving two-sided exponential selection

## Task status

The original existential conjecture remains unresolved. `Submission/Spec.lean`
is unchanged, with its original `sorry`. No main proof or disproof is submitted.

## Completed finite theorem

`Erdos66CompensatedPipage.exists_compensated_rounding` rounds any finite
nonnegative sum of representation exponential polynomials, allowing arbitrary
real tilts t, while preserving every prefix floor/ceiling bracket. It bounds
the final cost by the independent Bernoulli cost with each term multiplied by
exp(2|t|). This constant is independent of the number of coordinates and targets.

The earlier upper-only rounding theorem could not be used for negative tilts.
The new argument factors disjoint matching supports. Updating two coordinates
in distinct representation pairs is concave for either sign of the tilt. For
the exceptional target n=i+j, the potential ratio is at most exp(2|t|).

The pending flag records whether two fractional coordinates have sum at most n.
It decreases as fractional coordinates are eliminated. An ordered step on the
first two fractional coordinates i<j removes the pending flag at n=i+j. Thus a
single pending-target multiplier pays for all exceptional steps for each target.
The last fractional coordinate is rounded unbiasedly, rather than always down.

`Erdos66PrefixBalancedTwoSidedSelection.exists_prefix_balanced_selection` is
the Boolean-set wrapper.

## Completed infinite construction

`Erdos66PrefixBalancedCostCompactness.exists_balanced_summable_costs` extends
summable-cost compactness by retaining the closed prefix-discrepancy constraint.

`Erdos66PrefixBalancedExponentialCosts.exists_balanced_summable_rep_costs`
handles countably many nonnegative finite exponential combinations, with tilts
bounded by 1/2 and uniformly summable independent-Bernoulli mean bounds. The
uniform compensation exp(1) is absorbed into the row tail budgets.

`Erdos66PrefixBalancedPowerProfile.exists_balanced_power_potentials` applies
this to all reciprocal-integer two-sided power-tilted deviation potentials.
For any [0,1] fractional profile p with (p*p)(n)/log n -> c>0, it returns one A
with prefix discrepancy at most one and all of these potentials summable.

`Erdos66PrefixBalancedDensityOne.exists_balanced_density_one_profile` extracts
the joint endpoint. For the SAME A and c:

* every prefix has discrepancy <=1 from p;
* there is one harmonically summable, density-zero set E outside which the
  normalized representation function converges to c;
* for each fixed epsilon>0 there is alpha(epsilon) in (0,1), with summable
  exceptional weight (n+2)^(-1+alpha) and count o(N^(1-alpha));
* the existing constant-width all-target envelopes are retained.

The special case of the exact harmonic fractional profile is
`exists_harmonic_rounding_with_power_exceptions`.

## Verification

The following production files compile and have current oleans:

1. DisjointProductPipageExplore.lean
2. RepresentationPipageExplore.lean
3. CompensatedPipageExplore.lean
4. PrefixBalancedTwoSidedSelectionExplore.lean
5. PrefixBalancedCostCompactnessExplore.lean
6. PrefixBalancedExponentialCostsExplore.lean
7. PrefixBalancedPowerProfileExplore.lean
8. PrefixBalancedDensityOneExplore.lean

`CompensatedPipageAxiomCheck.lean` and `PrefixBalancedTwoSidedAxiomCheck.lean`
audit the principal declarations. Only propext, Classical.choice, and Quot.sound
occur. There are no new axioms or sorries in the production files.

## Main gap

The exceptional power saving can tend to zero with the tolerance. These results
do not give sub-square-root exception counts at every tolerance, an all-target
upper asymptotic coefficient c, or vanishing normalized quadratic rounding error.
In particular, they do not justify deleting the exceptional set from the limit.
The original conjecture is not proved or disproved.

## Compatibility review

Reconsidering the finite whole-block and slice-preserving constructions did not
supply an all-target gluing step. Equal-field complete-root formulas do not
control different-modulus mixed representations; the nearby-modulus quotient
term remains. Literal product extensions remain subject to the already proved
radix-gap and product-cube obstructions. None of these construction-specific
barriers is a negation of the existential conjecture.
