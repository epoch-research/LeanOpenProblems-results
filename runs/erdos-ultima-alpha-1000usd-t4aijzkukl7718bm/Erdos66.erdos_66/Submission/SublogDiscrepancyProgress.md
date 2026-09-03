# Sublogarithmic prefix discrepancy

The original conjecture remains neither proved nor disproved. `Spec.lean`
is unchanged and still contains its original `sorry`.

## Completed extension of the rounding criterion

`SublogDiscrepancyExplore.lean` weakens the bounded-prefix-discrepancy
hypothesis from `RoundingExplore.lean`.

For the exact fractional harmonic profile p and any error sequence e, it
proves

    (sum_{i<=n} e_i)/log n --> 0
      implies (e*p)(n)/log n --> 0.

The proof converts the hypothesis to a global envelope

    |sum_{i<=n} e_i| <= epsilon*H_n + D_epsilon.

The existing identity

    (e*p)(n) = E_n - (E*stepMass)(n)

and the nonnegative step-mass kernel with partial sums at most one give

    |(e*p)(n)| <= 2*(epsilon*H_n + D_epsilon).

Since H_n/log n tends to one and epsilon is arbitrary, the mixed term is
negligible.

Consequently, for e=1_A-p and prefix discrepancy o(log n),

    r_A(n)/log n --> 1  iff  (e*e)(n)/log n --> 0.

Main declarations:

- `mixed_log_limit_of_sublog_prefix`
- `sublog_prefix_limit_iff_quadratic_error`
- `sublog_rounding_suffices`

The last theorem explicitly assumes the existence of a set satisfying BOTH
required estimates. It is not an existence proof for such a set.

## Verification

The source file compiles and has a current olean. Principal declarations are
audited by `SublogDiscrepancyAxiomCheck.lean` and use only propext,
Classical.choice, and Quot.sound.

## Remaining gap

This enlarges the admissible class of rounding procedures; bounded prefix
discrepancy is no longer required. It still does not control the quadratic
self-convolution error. Neither deterministic nor dependent-random rounding
with the needed uniform quadratic estimate has been constructed.
