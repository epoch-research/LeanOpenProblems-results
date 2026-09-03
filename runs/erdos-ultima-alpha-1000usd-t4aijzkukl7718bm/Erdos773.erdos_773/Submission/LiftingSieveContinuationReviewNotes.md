# Lifting and sieve continuation review

The original conjecture remains UNSETTLED. No new theorem, exponent improvement,
near-linear Sidon construction, or original-conjecture disproof resulted from
this review. Submission/Spec.lean was not edited.

The current completed lower bound is the coefficient-one eventual bound
M(N) >= N^(2/3), from GreedyBatchSquareEndpoint.eventual_endpoint. The sole
remaining admission is the case 0 < epsilon < 1/3 of erdos_773.

## Routes reconsidered

* Root-translation and digit lifting still require actual cross-fiber positive-
  difference compatibility. Neither individual Sidonness nor modular pair
  matching supplies that compatibility. No new amplification inequality was
  obtained.
* The existing quadratic-residue scalar inequalities already have a common
  near-linear integer cardinality model for all positive moduli simultaneously.
  Optimizing just these inequalities cannot produce the required fixed-power
  disproof. This does not rule out a distribution-sensitive strengthening.
* The primorial upper bound has an exponent loss tending to zero. It remains
  compatible with the original conjecture; density zero is not its negation.
* Fixed-support S-unit and private-divisibility ideas were compared with the
  existing carrier-cardinality and private-modulus costs. No square-specific
  capacity-one selector was obtained.
* Formal Gaussian polynomial Sidonness still cannot be specialized to integer
  roots without carry control. Existing equal-histogram and distinct-digit
  counterexamples remain relevant, but do not resolve the exact full allowed-
  alphabet carrier. No new claim about that carrier was proved.

No numerical or SMT search was launched in this continuation. No proof was
submitted as a settlement. The conjecture statement and sole import remain
unchanged.
