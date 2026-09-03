# Carry-transfer review after arbitrary-modulus full fibers

This review did not settle Erdős 773 and did not change any Lean source.
Spec.lean retains the single sorry at line 2031, for 0 < epsilon <= 1/3.

The proved formal Gaussian construction remains genuinely Sidon in Z[X].
There is still no valid near-linear integer-specialization theorem.

Rechecked limitations:

* Fixed constant digits and monotone lower digits already have verified
  cubic specialization counterexamples (CubicGaussianSpecialization).
* Complete histograms, common digit norms, and small total digit sum do not
  give a blanket transfer rule (the existing inert-prime carry examples).
* All-distinct digits, fixed ends, and even prime bases have verified
  counterexamples under the precise hypotheses recorded in their notes.
* Imposing values or derivatives at auxiliary points would require a
  quantitative cardinality argument as well as a proof eliminating carries.
  Neither was obtained here. No claim that every such refinement fails is made.
* A generic additive modeling map of polynomial SQUARE VALUES does not
  automatically map those values to integer squares. Ring evaluation and
  ordinary additive modeling cannot be interchanged.
* Arbitrary sparse fibers can omit the collision endpoints in the new
  full-fiber bounds, so those bounds still cannot disprove the conjecture.

No new actual lower exponent, near-linear selector, or fixed-power upper
bound for arbitrary square-Sidon subsets was obtained. The reviewed
obstructions concern sufficient construction rules, not the negation of
the original quantified conjecture. No proof submission was made.

Main-file SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14
