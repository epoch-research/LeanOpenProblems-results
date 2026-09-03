# Uniform moving-window logarithmic averages for the explicit rounding

## Original task status

The conjecture remains unresolved. `Submission/Spec.lean` is unchanged and
still contains its original `sorry`. No valid proof or disproof has been
submitted. The results below are averaged results for one actual infinite
set; they are not the pointwise limit requested in Spec.lean.

## Explicit infinite set and strongest new theorem

Let

    A = Erdos66Rounding.roundedSet Erdos66Fractional.profile.

The fractional profile p has exact self-convolution H_(n+1), and A is the
previously checked floor rounding of its cumulative mass.

`Erdos66MovingWindowLimit.rounded_moving_window_limit_of_width` proves:

For ANY natural-valued width function w satisfying eventually

    0 < w(n) <= n

and

    n / (w(n)^2 * log n) -> 0,

the SAME fixed set A satisfies

    [sum_(n < k <= n+w(n)) r_A(k)] / [w(n) log n] -> 1.

Thus widths much larger than sqrt(n/log n) suffice. No choice of a new set
for each width or cutoff is used.

`rounded_sqrt_window_limit` specializes to w(n)=floor(sqrt(n))+1.
`rounded_moving_window_limit` gives the simpler sufficient eventual bounds
n<=w(n)^2 and w(n)<=n.

## Cumulative discrepancy bound

`CumulativeRoundingErrorExplore.lean`, namespace
`Erdos66CumulativeRoundingError`, proves:

If |sum_(i<=N) (1_A(i)-p_i)| <= D for every N, with D>=0, then

    |sum_(k<=N) (r_A(k)-H_(k+1))|
      <= 2D sqrt((2N+1) H_(2N+1)) + D^2.

This is unconditional within the bounded-prefix-discrepancy class; it does
not assume that the quadratic rounding error is pointwise small.

Proof ingredients:

* `prefix_convolution`: taking prefix sums commutes with convolution on
  one factor.
* `difference_of_convolution_squares`: a*a-p*p=(a-p)*(a+p).
* `bounded_prefix_convolution`: the prefix discrepancy bound and
  nonnegativity of a+p control the cumulative error.
* `prefix_square_le_convolution_prefix`: the square of the fractional
  prefix mass is bounded by the convolution mass through twice the cutoff.
* The exact harmonic convolution gives

      (sum_(i<=N) p_i)^2 <= (2N+1) H_(2N+1).

For the canonical rounding D=1.

## Quantitative moving-window bound

`MovingWindowRoundingExplore.lean`, namespace
`Erdos66MovingWindowRounding`, proves for 1<=n and w<=n:

    [sum_(n < k <= n+w) (r_A(k)-H_(k+1))]^2
      <= 200 n (1+log 5+log n).

The square is OUTSIDE the sum. This is a bound on the signed window error,
NOT on the sum of squared or absolute pointwise errors.

After division by w(n)^2 log(n)^2, the sufficient width condition makes
this tend to zero. Harmonic monotonicity and elementary logarithm bounds
show the reference window average divided by log n tends to one.

## Consecutive-square windows

The intermediate files

* `QuadraticWindowRoundingExplore.lean`
* `QuadraticWindowLimitExplore.lean`

prove the analogous limit on (n^2,(n+1)^2], with normalization
(2n+1) log(n^2). The later moving-window theorem is stronger in allowing
arbitrary centers and a general width function.

## Verification

All five new source files compile and have current oleans. The principal
results in `MovingWindowAxiomCheck.lean` use only propext,
Classical.choice, and Quot.sound. No new development file contains sorry
or admit.

## Remaining fine-scale gap

No pointwise O(log n) upper bound has been proved here for the rounded set.
No pointwise o(log n) quadratic-error estimate has been proved. The signed
averages allow cancellation and do not imply that individual deficits meet
the existing weighted summability condition for sparse completion.

Averaging cannot simply be replaced by an unweighted digit thickening or
independent thinning: those operations change the representation mean, and
no density-preserving conversion with the required pointwise control has
been established. This is the missing step in the coarse-to-fine proposal,
not a theorem excluding all such conversions.

## Subsequent limitation check

See `WindowPerturbationProgress.md`. A checked explicit sparse union preserves
ALL of the width limits here while its normalized pointwise counts have a
subsequence tending to infinity. Thus the full averaged result alone cannot
supply the missing pointwise conclusion.
