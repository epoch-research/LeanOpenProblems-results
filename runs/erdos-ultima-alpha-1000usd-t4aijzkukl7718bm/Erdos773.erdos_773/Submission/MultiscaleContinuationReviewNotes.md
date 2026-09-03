# Multiscale continuation review

The original conjecture remains unsettled. No Lean source was changed in
this continuation; Spec.lean still has its one admission for
0 < epsilon < 1/3. The two-thirds endpoint is already complete and was not
redone. No proof submission was made.

## Rotation and multiscale restrictions

Combining narrow root intervals with a common residue gives a stronger
cutoff for rotation denominators, but no improved density/cutoff tradeoff
was obtained. The old bounded-coefficient digit lifting lemma still needs
its explicit no-carry hypothesis. Normalizing a rotation by its denominator
makes the coefficients bounded but makes the digit discrepancies rational;
the integer signed-zero lemma cannot then be applied.

In the mixed-fiber discussion it remains essential not to identify the
small Gaussian factor with the rotation that respects the modular matching.
Swapping just one pair can replace the rotation by its complementary factor
but also swaps the modular matching. No universal small-denominator bound
for the matching-oriented rotation was proved.

## Full and partial fibers

Trying to choose better residue labels does not evade the already proved
aggregate full-fiber overlap bound. The existing weighted pigeonhole bound
applies without a pairwise uniform overlap estimate. Arbitrary partial
index sets can avoid the explicitly constructed endpoints, so the full-fiber
bound cannot be transferred to them without a new argument. No such
argument or compatible partial selector was found here.

## Other revisited candidates

* Generic bounded-capacity and near-critical ambient-density extraction
  are already excluded by the verified ordinary-integer counterexamples;
  those examples are not square-set counterexamples.
* Finite-field Sidon constructions still need a valid small-integer-root
  lift. Neither a Witt-coordinate discussion nor a thickened parabola
  supplied one.
* The full allowed multiples-of-six permutation alphabet remains unproved
  and unrefuted in this review. Existing fixed histograms, distinct-digit
  obstructions, and the full ORDINARY alphabet counterexample do not
  establish a result for that exact candidate.

These are records of unsuccessful checks, not new formal theorems and not
an upper or lower bound improving the original conjecture's exponent.
