# Residual frequent linear growth and logarithmic divergence

The original conjecture remains unresolved. `Submission/Spec.lean` is unchanged
and retains its original `sorry`. No proof of the universal statement or
irrational counterexample has been found, and no incomplete proof was submitted.

## Verified file

`Submission/GenericFrequentLinear.lean`, namespace
`Erdos972GenericFrequentLinear`, compiles. The principal declaration audits
list only `propext`, `Classical.choice`, and `Quot.sound`.

The main results are:

- `eventually_residual_frequently_linear_widePairs`
- `eventually_residual_frequently_linear_primeCorrelation`
- `eventually_residual_not_summable_prime`
- `eventually_residual_logPrimeCorrelation_tendsto`
- `eventually_residual_logMangoldtCorrelation_tendsto`

For a residual set of irrational slopes alpha, if alpha>1, the actual weighted
prime-pair correlation exceeds N/16 at arbitrarily large N. Consequently its
reciprocal-weighted series is not summable, and its partial sums tend to infinity.
The same divergence holds for the reciprocal-weighted Mangoldt correlation.

## Topological detail

The finite prime-pair boxes are half-open, so the rich-tail sets are not simply
asserted to be open. The finite counts are continuous at irrational slopes:
the only potential discontinuities occur at rational endpoints. Thus irrational
points of a rich-tail set lie in its interior. Combining this observation with
the earlier almost-everywhere result gives dense open augmented rich-tail sets.
Their countable intersection gives the residual result.

## Unchanged pointwise gap

A residual and conull successful set need not contain every irrational slope.
An exceptional irrational, if one exists, is not excluded by these results.

Revisiting the divisor-renewal route did not establish that finiteness at alpha
propagates to alpha*m, or to a positive-measure family of slopes. Even information
on a countable dense rational-multiplicative orbit could not by itself contradict
the residual or conull results, since such an orbit can be null and meagre.
No pointwise prime-correlation lower bound follows from the new theorems.

Compilation:

    lake env lean -o .lake/build/lib/lean/Submission/GenericFrequentLinear.olean \
      Submission/GenericFrequentLinear.lean
