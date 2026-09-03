# Compiled endpoint search

## Status

No proof or disproof of the original conjecture was found. Spec.lean is
unchanged with its original sorry. This search is not a mathematical
impossibility result and does not establish that no combination of lemmas
could settle the conjecture.

## Search performed

A source index found 125 theorem/lemma declarations mentioning existential
quantification, Tendsto, and sumRep in compiled development files. Their
statements include conditional completion criteria, masked exceptional-set
limits, zero-increment restoration limits, and necessary conditions under
an assumed witness. No unconditional original endpoint was identified.

Submission/AllProductionEndpointSearch.lean imports all 800 compiled
*Explore development modules and tests Lean's exact? tactic on:

1. the exact original existential proposition;
2. its negation, without changing any quantifier.

Both searches failed to close their goals. The scratch file intentionally
does not compile and is not a production dependency or a submission file.
Its output is saved at /tmp/erdos66_endpoint_search.log. The source-declaration
index is at /tmp/erdos66_limit_declarations.txt.

## Explicit hypotheses still missing

The direct completion criteria require an all-target asymptotic upper bound
and summable weighted lower deficits, or lower-exception counts with exponent
below one half at every fixed tolerance. The latest certified upper-clipping
criterion requires its original-host excess budget to be negligible on the
sqrt(N log N) scale. The Boolean-rounding criterion requires pointwise
sublogarithmic quadratic error. None of these crucial inputs was supplied
by the search or established in this pass.
