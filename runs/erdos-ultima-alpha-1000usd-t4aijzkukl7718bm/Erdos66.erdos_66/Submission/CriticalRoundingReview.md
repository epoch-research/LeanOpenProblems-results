# Review of the remaining pointwise Boolean-rounding problem

## Status

This continuation did not produce a new verified theorem, a witness, or a
disproof of Erdős 66. Submission/Spec.lean remains unchanged with its original
sorry. No proof was submitted.

## The sufficient criterion remains exact

For the checked harmonic fractional profile p, p*p(n)=H_(n+1), write
e=1_A-p. The checked decomposition is

    r_A(n)=H_(n+1)+2(e*p)(n)+(e*e)(n).

Sublogarithmic prefix discrepancy makes the linear mixed term negligible
relative to log n. The missing assertion is an EXISTENCE theorem for a
Boolean rounding with pointwise (e*e)(n)=o(log n). Count balance, moving-window
averages, and density-one control do not imply it.

The compensated two-sided pipage theorem was rechecked in the review; its
completion is not an outstanding task. Its available tail exponent still
scales with c epsilon^2 at mean c log n. The usual summed-tail certificate
therefore cannot be applied to all shrinking tolerances with c fixed. This
is a limitation of that certificate, not a proof that every dependent
rounding must fail.

## Directions considered without a completed argument

* Hierarchical or sign-pattern rounding still needs a sparse Boolean
  convolution estimate. A dense signed-polynomial estimate cannot simply
  be substituted for it.
* Shared-point repair of many bad targets requires joint incidence control
  on the actual modification set. The previously checked signed-repair
  energy condition is necessary but supplies no such sufficient bound.
* Point-dependent routing and changing-field constructions are not ruled
  out by the fixed-field routing peak theorem. No all-intermediate-scale
  natural construction from them was obtained.
* Complete fixed-field transfer retains an integer-valued coarse weight
  profile. It does not let one insert the real fractional profile as an
  actual coarse family, and it does not itself create a better source.

These observations are not claimed as new impossibility theorems. No
additional sufficient hypothesis has been established that permits applying
the existing rounding, compactness, or completion criteria to Spec.lean.
