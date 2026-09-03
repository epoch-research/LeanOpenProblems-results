# Prime-row parity and exponentially small corrections

This is verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
`Spec.lean` remains unchanged with its original `sorry`. No complete solution
or submission was obtained in this continuation.

## Verification

`PrimeMultiplierParity.lean` compiles without warnings and has a built olean.
All five printed principal axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof holes.

## Uniform correction estimate

For prime p and positive j with 6*j^j<=p, let

    C = p*(j*(p-1))!/(p!)^j,
    eps = (j*(p-1))!/[(p!)^j*(p!-1)].

The preceding quantitative multinomial estimate gives

    C <= (j^j)^p,
    (2*j^j)^p <= p!,
    2^p*C <= p!.

Since C>=1, it follows that C*(2^p-1)<=p!-1. The exact identity
`eps=C/[p*(p!-1)]` then yields the new verified bound

    0 < eps <= 1/[p*(2^p-1)].

Thus the correction is exponentially small in p throughout the explicit
varying-multiplier range, not merely less than 1/p.

## Formula for both parities

The new `row_formula_mod` first proves

    fract((j*(p-1))!/(p!-1)) = (C mod p)/p + eps.

It separates the natural quotient and remainder of C by p and uses the
strict correction bound to ensure there is no carry across the next integer.
The previously verified prime congruence is

    C == (-1)^(j-1) (mod p).

Consequently:

* if j is even, the row is 1-1/p+eps (the earlier formula);
* if j is odd, the row is 1/p+eps (`odd_row_formula`).

The latter is valid also at j=1, although then the row index p exceeds the
factorial index p-1. It is a statement about the defined individual row
fractional part, not a claim that this row belongs to the corresponding
finite prefix of the full sum.

## Consecutive multipliers

For positive even j, assume the explicit size conditions for BOTH j and j+1.
The theorem `paired_row_bounds` proves

    1 < fract((j*(p-1))!/(p!-1))
          + fract(((j+1)*(p-1))!/(p!-1))
      <= 1 + 2/[p*(2^p-1)].

The two fractional parts are taken at different factorial indices but at
the same prime row p. Their correction terms add and are strictly positive.
This is not a statement about the sum of two full rowwise remainders.

Principal declarations:

* correction_pos
* factorial_ratio
* correction_eq
* numerator_pos
* factorial_dominates_numerator
* correction_le
* correction_lt_inv
* row_formula_mod
* odd_row_formula
* paired_row_bounds

## Remaining gap

The other rows cannot be discarded when forming a linear combination of
full tails. The small positive excess for this individual prime-row pair
does not itself yield a small nonzero integer linear form in the original
sum, and it does not contradict eventual integrality of full rowwise tails
under hypothetical rationality. No applicable cancellation or bound for
the remaining rows was established in this continuation.

No numerical experiment was run. All compilation and axiom audits have
completed; nothing remains pending. No submission check was made.
