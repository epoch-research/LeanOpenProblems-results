# Logarithmic-derivative product review

This is informal mathematical analysis, NOT a Lean proof or a settlement.
The original theorem in Spec.lean remains unchanged with its sorry.

A product different from the one in EntireProductNotes.md is

    P(z) = product_(n>=2) (1-z/n!).

Local uniform convergence follows from sum 1/n! < infinity. At z=1,
P(1)>0, and logarithmic differentiation gives

    -P'(1)/P(1) = sum_(n>=2) 1/(n!-1).

The factorially spaced zeros make P an entire function of order zero.
However its Taylor coefficients are NOT rational coefficients available
for integer clearing. Already P'(0)=2-e. Higher coefficients are infinite
elementary symmetric sums in the reciprocal factorials. Finite products
have rational coefficients, but their logarithmic derivatives at one are
just the original partial sums; this does not improve their denominator
versus tail-error problem.

By contrast, the product product_(n>=2) (1-z^n/n!) from the earlier notes
has integer factorial-scaled Taylor coefficients and order-two growth.
One must not combine the order-zero bound of the former product with the
arithmetic property of the latter. No irrationality theorem for either
exact product has been established here.

A further review compared the exact local tail hypotheses in
UnitTailSeparation, SubquadraticTailCriterion, and
StrictLinearLowerTailCriterion with CongruencePreservingCarry. The local
intervals include prime indices. The available bound T_n<n at composites
does not replace the missing small bound at the primes; the known
T_p<p^2 does not meet the displayed local size inequality. Moreover the
conditional rational prime-gap pattern already explains how tails near
p^2 can satisfy these arithmetic constraints without contradiction.

No new infinite nonvanishing, carry-divisibility, or fixed-factor prime-tail
bound was obtained. These checks give no complete proof or disproof, and
no proof has been submitted.
