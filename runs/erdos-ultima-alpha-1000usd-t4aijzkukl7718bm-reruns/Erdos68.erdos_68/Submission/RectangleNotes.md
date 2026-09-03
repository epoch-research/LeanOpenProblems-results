# Rectangular geometric truncations: verified obstruction

This is NOT a proof or disproof of Erdős 68. `Submission/Spec.lean` remains
unchanged.

Write alpha = sum_(n>=2) 1/(n!-1). For N>=2 and R>=1 define

    A_(N,R) = sum_(n=2)^N sum_(r=1)^R 1/(n!)^r.

`RectangleBarrier.lean` proves, for the REDUCED rational denominator Q of
A_(N,R),

    N^R divides Q,
    alpha - A_(N,R) > 2^(-R),
    Q * (alpha - A_(N,R)) > 1.

Thus reducing the rectangle's rational sum cannot rescue this entire
approximation family. This is stronger than merely observing that the
obvious termwise-clearing multiplier (N!)^R makes the error too large.
It does not exclude nonrectangular truncations, signed approximants, or
other constructions.

## Arithmetic proof

Let C_(N,R) = (N!)^R A_(N,R), an integer. It satisfies

    C_(N,R) = N^R C_(N-1,R) + sum_(j=0)^(R-1) (N!)^j.

Consequently C_(N,R) = 1 (mod N), so C_(N,R) is coprime to N^R.
The identity

    Q * C_(N,R) = P * (N!)^R

for A_(N,R)=P/Q in lowest terms therefore implies N^R | Q.
The omitted geometric tail of the n=2 row is exactly 2^(-R), and
there are additional strictly positive omitted terms. Hence

    Q*(alpha-A_(N,R)) > N^R / 2^R >= 1.

## Lean indexing and verification

* `rectangleApprox (n+1) r` corresponds to N=n+2 and R=r+1.
* `rectangleApprox_eq_sum` identifies the recursively defined rational
  with the finite rectangular sum.
* `rectangleNumerator_coprime` is the congruence/coprimality step.
* `rectangle_den_dvd` proves divisibility of the reduced denominator.
* `rectangle_error_lower` proves the strict analytic lower bound.
* `rectangle_reduced_scaled_error_gt_one` is the final obstruction.

The file compiles, and its final axiom check lists only propext,
Classical.choice, and Quot.sound. No hole remains in this auxiliary file.
