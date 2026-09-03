# Positive squared-factorial-small perturbations can have rational total

This is verified auxiliary progress, not a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and still contains its original `sorry`.

`Submission/PositiveSmallCorrectionRational.lean` compiles without warnings;
its olean has been built. The printed axiom audits for the sum and limit
use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact different series

For original indices n>=2, put

    c_n = (4n^2-3)/(2n+1)!,
    r_n = 1/n! + c_n.

The file verifies

    c_n > 0,
    sum_(n>=2) r_n = 5/6,
    (n!)^2 c_n -> 0.

Thus a positive correction that is even o(1/(n!)^2) need not preserve the
irrationality of the reciprocal-factorial sum. These terms are NOT the
original terms 1/(n!-1), nor are they asserted to be reciprocals of integers.

## Algebra and estimates

The exact pairing identity is

    c_n = (2n-2)/(2n)! + (2n-1)/(2n+1)!.

Summing pairs covers all k>=4 in the series (k-2)/k!. Since

    (k-2)/k! = 1/(k-1)! - 2/k!,

the factorial sums cancel, giving 5/6 after adding sum_(n>=2) 1/n!.
The proof uses summable shifts and `tsum_even_add_odd`.

The estimate

    4^n (n!)^2 <= (2n+1)!

is proved by induction. Consequently

    0 < (n!)^2 c_n <= 4n^2 / 4^n -> 0.

The Lean indexing is shifted by two. Main declarations are `tsum_term`,
`correction_pos`, `term_gt_reciprocal_factorial`,
`normalized_correction_bound`, and `normalized_correction_tendsto`.

## Scope

This comparison rules out an argument based only on positivity and the
squared-factorial decay of the correction to 1/n!. It does not address a
construction that also uses the exact integer denominators n!-1 with
adequate arithmetic height control. No such complete construction was
obtained, and no proof or disproof of the original conjecture was submitted.
