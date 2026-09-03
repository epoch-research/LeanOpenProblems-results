# Moving Lambert row cutoffs: a verified quadratic obstruction

This is auxiliary work, not a proof or disproof of Erdős 68.
`MovingLambertTailBarrier.lean` compiles, its olean has been built, and both
main theorem axiom checks list only `propext`, `Classical.choice`, and
`Quot.sound`.

Write A_m^(K) for the Lambert coefficients retaining only rows d>=K, and

    T_n^(K) = n! [sum_(m>=0) A_m^(K)/m! - sum_(m=0)^n A_m^(K)/m!].

## Uniform bound

`moving_lambert_tail_ge_square` proves

    n >= 18 and K <= floor(n/2)+1  ==>  T_n^(K) >= n^2.

Unlike the earlier fixed-cutoff obstruction, K may vary with n, and the
bound holds at every index meeting these hypotheses.

Take d=floor(n/2)+1. Then n<2d<=n+2. Keeping only the row-d contribution to
coefficient 2d gives

    T_n^(K) >= n!/(d!)^2.

The helper `central_factorial_square_bound` proves by induction that

    (2k+1)^2 ((k+1)!)^2 <= (2k)!       for k>=9.

Consequently n^2 (d!)^2<=n! for every n>=18. Positivity of the other terms
completes the bound. `scaledTail_ge_later` supplies the general estimate
from any later nonnegative coefficient, not only the next coefficient.

## Consequence for termwise factorial clearing

`cleared_moving_lambert_tail_ge_square` proves

    K >= 10 and ((K-1)!-1) divides n!  ==>  T_n^(K) >= n^2.

The previously verified `FactorialClearingIndex.not_dvd_double_factorial`
shows that clearing this denominator requires n>2(K-1). Hence n>=19 and
K<=floor(n/2)+1, so the uniform theorem applies.

Thus even allowing the removed initial row block to grow cannot supply the
new local small-tail condition if the factorial multiplier clears the last
removed denominator termwise. Its resulting tail is already at least n^2.

## Essential limitation

Divisibility of the reduced denominator of a sum does NOT imply termwise
clearing of its last summand. Cancellation in a removed row sum remains
outside this result. No adequate reduced-denominator estimate or alternative
small-tail representation has been obtained.

`Submission/Spec.lean` remains unchanged with its original `sorry`. No proof
or disproof of the conjecture has been submitted.
