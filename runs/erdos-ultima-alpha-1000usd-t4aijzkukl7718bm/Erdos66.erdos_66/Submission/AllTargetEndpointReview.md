# Endpoint review after certified global upper clipping

## Status

This review produced no new theorem settling Erdős 66. Spec.lean remains
unchanged with its original sorry. No proof or exact-negation theorem was
submitted. The most recent compiled positive result remains the conditional
CertifiedGlobalUpperClippingExplore.lean theorem, documented separately.

## Definitions checked

FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean defines
sumRep as the ordinary ordered self-convolution of a natural set indicator.
There is no definitional mismatch that makes the original proposition trivial.
The conjecture asks for a finite real nonzero limit along every natural target.

## Obstruction endpoint

The verified Abel error-energy and higher-moment results still yield only
square-root-logarithmic necessary fluctuations. Generic growing-order Gaussian
moment amplification is already refuted by the checked finite cyclic and
natural-annulus counterexamples. The original limit allows an unbounded
error o(log n), so neither a bounded-error obstruction nor the current energy
lower bounds give its negation.

Parity splitting gives a pointwise mixed limit and a combined self-count
limit, but only mean-square control of the imbalance. The review did not find
a valid implication to separate pointwise self-count limits. Coefficientwise
Cauchy--Schwarz cannot be applied as though reflection convolution were a
positive-definite inner product.

## Construction endpoint

The local finite constructions can collapse many fine targets into a smaller
coarse test family. The unresolved step remains compatibility across changing
periods and control of the first transition window. The exact compactness
criterion still requires one nonzero coefficient and the entire threshold
function before the final finite cutoff.

Rudin--Shapiro recursion was reconsidered, then the existing
RecursiveRoundingReview.md was located. The same coupled square/mixed-product
recurrence was already examined there. Exact finite coefficient calculations
are not a uniform estimate and are not a new asymptotic theorem. No sparse,
biased Boolean rounding satisfying pointwise (e*e)(n)=o(log n) was constructed.

A Cantor-measure or refining-grid analogy also supplies no direct natural-set
construction: consistency under rescaling is not consistency of natural-number
prefixes, and a singular macroscopic profile cannot be silently substituted
for the smooth counting profile forced by a hypothetical witness.

## Reference check

A fresh request to https://www.erdosproblems.com/66 failed with curl error 6
(could not resolve host); getent likewise returned no DNS entry. No new
external result was obtained, and no claim about a published resolution is
being made.

## Remaining actual requirements

A solution still needs an all-target Boolean witness, sufficient uniform finite
prefix feasibility, a completion input with the missing quantitative budgets,
or an obstruction of logarithmic size applying to every possible witness.
None was obtained in this review.
