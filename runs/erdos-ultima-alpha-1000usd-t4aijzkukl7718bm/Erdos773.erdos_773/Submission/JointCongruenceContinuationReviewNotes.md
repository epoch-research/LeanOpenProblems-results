# Joint-congruence continuation review

No new theorem or settlement resulted from this review. Spec.lean is unchanged,
with the sole sorry at line 17287, for 0 < epsilon < 1/3. The actual completed
endpoint remains eventual M(N) >= N^(2/3).

Rechecked QuadraticResidueDensityLower.lean. Its integer_cardinality_model
already treats all positive moduli simultaneously, not just a separately
optimized modulus. The inequalities in that result remain scalar cardinality
constraints. A distribution-sensitive sieve could in principle say more; no
claim that all such stronger sieves fail was proved here.

Also reconsidered weighted difference-capacity constraints. The previously
proved fractional results cannot be rounded merely from their simultaneous
validity. Generic bounded-capacity obstructions still do not constitute square-
set counterexamples, and they supply no disproof of the original conjecture.

Reviewed possible use of Cartesian subfamilies of the permutation carrier,
reflection and digit-permutation symmetries, and principal-unit digit lifting.
No proof transferred a full-fiber or universal-affine height ceiling to the
sparse fibers or selected affine maps actually available. No cross-fiber
compatibility or improved amplification inequality was obtained.

A disproof of the original conjecture still requires a fixed positive power
saving on an unbounded sequence of heights. The existing primorial upper bound
has a loss tending to zero in the exponent and does not provide that saving.
No original-conjecture proof, disproof, new Sidon exponent, or new carrier
collision was obtained in this continuation.

No new search was launched and no incomplete main proof was submitted.
