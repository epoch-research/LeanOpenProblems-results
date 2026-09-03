# Reciprocal-weighted error: verified, conjecture still unresolved

Spec.lean is unchanged and still contains its original sorry. No proof or
irrational counterexample has been found. Do not submit as complete.

## Completed files

ReciprocalPrefixSummability.lean proves that a nonnegative sequence a with

    sum_{k<=N} a(k) <= C (N+1)^s,   C>=0, s<1,

has a summable reciprocal-weighted series sum a(n)/(n+1). The proof uses
finite summation by parts and the convergent p-series of exponent s-2.

LogCorrelationCriterion.lean defines the actual nonnegative error

    powerErrorTerm(alpha,n) = Lambda(n) Lambda(floor(alpha*n))
      - 1_{n and floor(alpha*n) prime} log(n) log(floor(alpha*n)).

For every alpha>=1, it proves:

- `summable_powerErrorTerm_div_succ`: sum error(n)/(n+1) is summable.
- `summable_mangoldt_iff_prime`: the reciprocal-weighted Mangoldt series
  and genuine prime-pair series have the same summability behavior.
- `logCorrelation_error_bound`: their finite partial sums differ by a
  nonnegative quantity bounded by the single finite total error sum.
- `infinite_primeSet_of_unbounded_logCorrelation`: unboundedness of the
  reciprocal-weighted Mangoldt partial sums implies prime-pair infinitude.

The unboundedness hypothesis has NOT been proved for every irrational slope.

## Important growth qualification

Arbitrarily slow unbounded growth of the RECIPROCAL-WEIGHTED correlation is
sufficient in the last theorem. It must not be confused with arbitrarily slow
growth of the UNWEIGHTED correlation.

In particular, this criterion is NOT weaker than all the earlier sublinear
power criteria. `logCorrelation_bounded_of_power_bound` verifies that any
global O(N^s) bound with s<1 on the unweighted correlation makes the reciprocal
correlation bounded. A frequently positive N^s lower bound for 1/2<s<1 can
suffice for infinitude without implying reciprocal divergence.

## Analytic review

Averaging the existing good-scale identities does not eliminate their signed
four-factor remainder. There is no proved lower bound for that remainder's
weighted average. Likewise, the compact-frequency prime-ratio pole estimates
do not resolve the floor strip, whose logarithmic width shrinks as 1/n.
Reciprocal weighting does not make that width fixed. No new signed estimate
or pointwise prime-pair lower bound was obtained in this review.

All printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound. No change to the original import or conjecture was made.
