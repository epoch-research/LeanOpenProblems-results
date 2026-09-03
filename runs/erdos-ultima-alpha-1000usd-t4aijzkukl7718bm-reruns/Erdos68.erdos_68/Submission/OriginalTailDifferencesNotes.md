# The original scaled tail is not completely monotone

This auxiliary result does not prove or disprove Erdős 68. The conjecture in
`Spec.lean` remains unchanged and unproved.

`OriginalTailDifferences.lean` compiles without warnings and has a built
olean. Both principal axiom audits list only `propext`, `Classical.choice`,
and `Quot.sound`.

For the original sum alpha, put

    U(n) = n! * (alpha - sum_(m=2)^n 1/(m!-1)),  n>=1,
    delta f(n) = f(n)-f(n+1).

In contrast to the factorial-power tails in
`CompletelyMonotoneDifferences.lean`, this sequence is not completely
monotone. The verified counterexample is

    delta^28 U(4) < 0.

The Lean definition `originalTail n` is U(n+1); the theorem is therefore
`negative_difference : diff 28 originalTail 3 < 0`. It implies
`originalTail_not_completely_monotone`.

The certificate is exact, not a floating-point decision. The binomial
finite-difference formula gives

    delta^28 U(4) = a*alpha-b,
    a = 109499087816928489496181139030903384,

with the explicit rational b recorded in the file. Its unreduced status is
irrelevant to the inequality. The already verified Farey interval yields

    alpha < 125349875569995347164336093790579894036923220833202 / 10^50,

and exact rational arithmetic proves a times this upper bound is less
than b. The approximate value -1.9646435244e-7 is diagnostic only.

The file also verifies the general conversion between the backward-sign
iterated difference used here and Mathlib's forward-difference operator.

## What this excludes

Positivity and the Newton order bound for the individual scaled
factorial-power tails cannot simply be applied to U. In the geometric
expansion, U has the extra n-dependent factors (n!)^(1-j); taking differences
does not commute with treating these factors as constants.

This result supplies no small integer form in alpha. In particular, b has
a large rational denominator, and neither rationality of alpha nor the
small real value of a*alpha-b makes it an integer. No settlement of the
original conjecture has been obtained or submitted.
