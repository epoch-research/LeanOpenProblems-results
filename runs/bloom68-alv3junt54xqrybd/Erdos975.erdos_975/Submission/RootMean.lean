import Submission.RootMeanGeneral

/-!
# Positive root-count means for all irreducible integer polynomials

This entry module exposes `Erdos975Support.exists_pos_rootMean_of_irreducible`:
for every nonconstant irreducible `f : ℤ[X]`, there is a strictly positive
constant `κ` such that `rootCountSummatory (polynomialAbsValue f) N / N`
tends to `κ`. Neither monicity nor eventual positivity is needed for this
root-count assertion.

The proof uses actual finite-modulus Hensel lifting, the number field of the
monic integral normalization, Kummer–Dedekind at good primes, the ideal norm
mean, and a proved absolutely summable, positive Euler correction. The
correction is applied to the original polynomial's root coefficients,
including the leading-coefficient bad primes; agreement at good primes alone
is not treated as sufficient.

`RootMeanGeneral` also proves the full divisor-average conclusion for all
admissible polynomials of degree at most two. `ConjectureReduction` separately
proves the exact equivalence between the unrestricted conjecture and finite
normalized balanced-divisor limits for the admissible polynomials of degree
at least three. Those high-degree limits remain unproved here.

All mathematical declarations are in `Erdos975Support`. This module does not
import the specification or use either of its admitted declarations. The
complete root-mean and low-degree import graph is checked by
`RootMeanGeneralAudit`; `RootMeanAudit` retains an audit of the original eight
prerequisite modules.
-/
