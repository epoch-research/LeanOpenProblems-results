# Sharper row-tail bounds (verified auxiliary progress, not a settlement)

`SharperRowRemainderBounds.lean` strengthens the quantitative estimates from
`RowRemainderBounds.lean`. It does not prove or disprove Erdős 68, and
`Submission/Spec.lean` remains unchanged.

Let alpha be the original sum and define

    F_n = sum_(k=2)^n floor(n!/(k!-1)),
    T_n = n!*alpha-F_n.

## Main verified estimates

For positive natural J,L, n>=2, and n>=(2 J^2)^L,

    T_n/(n+1) <= 1/J + (1+log J)/L + (J+1)/(n+1)
                  + 2/2^n + 3/(n+1)^2.

This is `rowTail_normalized_bound_sharp`. Both the threshold and the band-count
term improve on the earlier bound, which used n>=2^[L(J^2+1)] and J/L.

Taking J=L=2^s gives `rowTail_dyadic_bound`. Absorbing the three small errors
then gives the particularly simple `rowTail_explicit_bound`:

    n >= 2^[(2s+1)2^s]  ==>  T_n/(n+1) <= (s+5)/2^s.

These are all-index inequalities under the stated explicit thresholds, not
numerical experiments. No separate theorem using asymptotic Big-O notation
is asserted in this file.

## Improved factorial-block estimate

`factorial_block_bound` proves

    (Ck)! <= C^(Ck) (k!)^C.

Induct on k. The C new factors in (C(k+1))! are at most C(k+1), giving the
bound using `Nat.ascFactorial_le_pow_add`.

For C=floor(n/k)+1, one has Ck<=2n. If C<=J, then

    C^(Ck) * 2^n <= (2J^2)^n.

The hypotheses n>=(2J^2)^L and Ck-n>floor(n/L) therefore imply

    n! * 2^n <= (k!)^C.

The previous integer geometric-prefix argument now bounds the fractional
remainder of every such row by 2/2^n. This is
`factorial_power_large_sharp` and `row_fraction_small_sharp`.

## Harmonic counting of transition bands

Put H=floor(n/L). A row in the exceptional band, with C=floor(n/k)+1,
satisfies

    floor(n/C) < k <= floor((n+H)/C).

For fixed C this interval contains at most floor(H/C)+1 integers. Taking
a union over 1<=C<=J bounds the band cardinality by

    sum_(C=1)^J (floor(H/C)+1) <= H*(1+log J)+J.

This is `transitionBand_card_sharp_nat` and `transitionBand_card_sharp`.
Combining that count with the small rows k<=floor(n/J), the tiny remaining
fractions, and the existing omitted-tail bound proves the main estimate.

## Verification and limitation

The file compiles, its olean has been built, and the printed axiom checks for
the three main bounds list only `propext`, `Classical.choice`, and `Quot.sound`.

Rationality of alpha would make T_n a positive integer eventually. These
sharper bounds still allow positive integral tails; they prove no nonintegrality
and no new coefficient congruence. The earlier necessary residue condition
therefore remains unexcluded. No proof of the original conjecture has been
submitted.

## Explicit necessary residue interval

The further theorem `rowCoeff_residue_bounds_of_rational` now verifies the
quantitative consequence for

    c_n = F_n-n F_(n-1).

If alpha=q is rational, n>=3, q.den<n, and n>=2^[(2s+1)2^s], then

    1 - 2(s+5)/2^s <= (c_n mod n)/n < 1.

The factor 2 merely converts T_n/(n+1) to T_n/n. This theorem also compiles
with only the permitted axioms. No violation of the necessary interval at
arbitrarily large indices has been proved, so this does not settle the
conjecture.
