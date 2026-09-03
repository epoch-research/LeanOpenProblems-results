# Capacity criterion for a single coefficient sequence

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original sorry. No final proof was submitted.

## New checked file

QuarticPrefixCapacityExplore.lean instantiates the previous abstract block
energy criterion with the geometric blocks of ONE sequence x : Nat -> Real.
It compiles without warnings and has a current olean. Its eight declarations
are audited in QuarticPrefixCapacityAudit.lean; the saved log uses only
propext, Classical.choice, and Quot.sound.

## Actual sequence theorem

If sum_i x(i)^4 is finite, then

    sum_n [sum_(i<4^n) x(i)^2]^2 / 4^n

is finite. In particular, for every c>0 and N there is n>=N such that

    (n+1) [sum_(i<4^n) x(i)^2]^2 < c 4^n.

The proof partitions the coefficient indices into [0,1) and
[4^n,4^(n+1)), applies finite Cauchy--Schwarz to each block, and invokes
the checked geometric-prefix energy estimate. The block partition and its
exact finite prefix-sum identity are proved in the new file.

## Conditional support/capacity form

If, additionally, a sequence q satisfies eventually

    4^n <= q(n) sum_(i<4^n) x(i)^2,

then for every C>0 and N there is n>=N such that

    q(n)^2 > C 4^n (n+1).

This uses the previous scalar capacity theorem, with the actual fourth-power
block sums as its summable energy sequence. No Fourier or measure-theoretic
instantiation is asserted here.

## Main application check

The old finite-field results preserve an embedded SLICE, while the natural
prefix theorems preserve finitely many memberships. Neither supplies one
fixed coefficient sequence x with the above summability and uncertainty
properties at all geometric resolutions.

In particular, CyclicPrefixPatchExplore already proves logarithmic cyclic
flatness with an ARBITRARY prescribed coordinatewise natural-prefix limit.
This includes limits with no relation to the desired natural representation
asymptotic. Consequently prefix agreement and finite cyclic flatness alone
cannot be substituted for the missing coefficient/energy compatibility.

No such coefficient sequence was extracted from a hypothetical witness to
Erdos66.erdos_66. The new criterion therefore remains conditional and is not
a disproof of the existential conjecture. The all-scale construction or
universal fluctuation gap is still open in this development.
