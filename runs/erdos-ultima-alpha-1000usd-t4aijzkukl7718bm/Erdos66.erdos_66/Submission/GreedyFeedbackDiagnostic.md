# Finite diagnostic of one-step logarithmic feedback

## Status

This is a numerical construction diagnostic, not a Lean theorem, a certified
counterexample, or a resolution of Erdős 66. Spec.lean is unchanged with its
original sorry. No proof was submitted.

## Rule tested

`Diagnostics/greedy_log_feedback.py` starts with A={0}. At step n it inserts n
if the already formed ordered sum count at n is less than c*log(n+2).
Insertion updates all sums with previously selected points, with weight two
for the two orders and weight one at the diagonal 2n.

The integer representation updates are exact; the logarithmic comparisons
use floating point. Results are diagnostic only. The test does not impose a
global future cap and does not delete any previously selected point.

## Runs

At N=1,048,576:

* c=1 selected 393,219 points, versus the hypothetical witness counting
  scale 2*sqrt(N log(N)/pi), approximately 4,302.
* c=16 selected 349,724 points, versus the corresponding scale approximately
  17,208.
* Both runs had very large representation peaks. In the final dyadic window,
  the maximum observed r(n)/log n was about 28,364 for c=1 and 25,179 for c=16.

For c=1, the selected points in the final window occupied exactly residues
1,4,7 modulo 8. This is an observation about that finite window, NOT a proved
eventual-periodicity assertion.

Saved arrays and logs are under /tmp/greedy_log_feedback_*.

## Outcome

The diagnostic supplies no useful all-scale invariant for this feedback
rule. It also supplies no mathematical conclusion about other feedback
rules, other candidates, or the original existential conjecture. No uniform
sublogarithmic rounding estimate or compatible transition construction was
obtained in this continuation.
