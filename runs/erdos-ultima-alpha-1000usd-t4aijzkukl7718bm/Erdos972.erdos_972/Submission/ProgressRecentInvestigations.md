# Recent investigations — no settlement

The conjecture in Spec.lean remains unchanged and unproved. No irrational
counterexample or sufficient prime-pair lower bound has been found. Do not
submit the unchanged sorry as a completed proof.

The only new Lean-verified result in these recent continuations is the
quadratic-floor recurrence and its three-prime-chain exclusion, documented
in ProgressQuadraticRecurrence.md. These do not prove finiteness of prime
pairs. Subsequent investigations produced no additional Lean declarations.

Unsuccessful routes considered (informal observations, not new theorems):

* A mean-two Selberg majorant would require mixed and joint error control
  at cutoffs beyond the proved row ranges. The needed estimates cannot be
  assumed merely because the majorant and its residual are nonnegative.
* Averaging binary prime counts over shifts does not directly handle the
  floor constraint: the shift is linked to a particular input interval.
  Good average behavior in all shifts does not imply good behavior in
  those linked intervals.
* Iterating an almost-prime factorization does not preserve an exact floor
  relation at a fixed slope. Relative approximation errors can still be
  large in absolute value, so compositeness cannot be transferred.
* For alpha between one and two, hypothetical composite outputs allow a
  descending factor tree. Positive additive leaf weights and logarithmic
  growth bounds by themselves give no contradiction.
* Ordinary Beatty partition theorems, prime-pattern results with additional
  free variables, and prime counts in long intervals do not enforce both
  primalities in the thin strip q <= alpha*p < q+1.
* In a balanced four-factor expansion, two near-equalities with the same
  outer variables can restrict an integer determinant to a short range.
  No signed estimate for the actual Mobius-weighted sum follows yet.
  Cauchy-Schwarz or unsigned energy bounds still do not give the needed
  strict lower gap. No inverse theorem was proved.

Library checks again found no applicable theorem supplying simultaneous
prime input and prime output. There is no pending successful proof edit,
compilation repair, or final submission.
