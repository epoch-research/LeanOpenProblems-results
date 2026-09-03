# Square-specific continuation review

The original conjecture is not settled. No new Lean theorem or improved
bound was obtained in this review. Spec.lean has not been edited, and the
known-incomplete submission has not been resubmitted.

The exact original quantifiers and definitions were rechecked. The unresolved
range remains 0 < epsilon <= 1/3. The strongest actual lower bound remains
the separately verified eventual N^(2/3)/36 bound.

## Formal-polynomial and digit routes

The verified Gaussian-Eisenstein polynomial construction is not an integer
construction. Existing specialization counterexamples also cover the exact
formal family at a prime base. The histogram and growing-moment results do
not control the number of surviving carry collisions. This review supplied
neither such a count nor a carry-safe large subclass.

## Residue correlations and short translated intersections

The scalar modular inequalities are already compatible with near-linear
cardinalities simultaneously for every modulus. Retaining correlations
between residue classes could in principle do more, but no implication from
those correlations to a new actual integer collision was proved here.

The extracted finite cubes of short translates do not imply the universal
affine-Sidon hypothesis. Their base sets remain sparse, and they do not
satisfy the full-fiber hypotheses of the existing construction-specific
upper bounds. No transfer of those upper bounds to arbitrary Sidon square
sets was found.

## Coefficient-one endpoint

The uniform eventual incident coefficient 333/1000 is below 1/3. Together
with an appropriate asymptotically sharp four-uniform greedy extraction
constant, this would be useful for the coefficient-one endpoint. The
existing verified extraction theorem does not have that constant. The
survival-aware and moving-mean certificates still lack the sharp numerical
shrinking-scale bootstrap and concentration application. No new work on
that bootstrap was formalized in this review.

Even the coefficient-one endpoint would not settle any epsilon < 1/3.
There is still no actual exponent-improving square-specific selector and
no fixed-power upper bound for the unrestricted maximum.

Fresh main-file check: /tmp/spec-square-specific-review.log.
